/* radare - LGPL - Copyright 2019 - xvilka */

/* SREC format description:
 * "S"TCC<AAAA[AA[AA]]>D...CC
 * T - 0-9, type of the record
 * BB - bytes count, two hex digits
 * AAAA[AA[AA]] - 4, 6 or 8 hex digits of the address (determined by the record type)
 * D... - data
 * CC - two bytes is the checksum
 *
 * S0 - header
 * S1 - 16bit addressed data (4 hex digits of the address)
 * S2 - 24bit addressed data (6 hex digits of the address)
 * S3 - 32bit addressed data (8 hex digits of the address)
 */

#include "r_io.h"
#include "r_lib.h"
#include "r_util.h"
#include <limits.h>	//for INT_MAX
#include <stdio.h>
#include <stdlib.h>
#include <sys/types.h>

//struct Rsrec : holds sparse buffer + its own fd, for internal management
typedef struct {
	int fd;
	RBuffer *rbuf;
} Rsrec;

static int fw04b(FILE *fd, ut16 eaddr);
static int fwblock(FILE *fd, ut8 *b, ut32 start_addr, ut16 size);

static int __write(RIO *io, RIODesc *fd, const ut8 *buf, int count) {
	eprintf ("NOT IMPLEMENTED!\n");
	return -1;
}

static int __read(RIO *io, RIODesc *fd, ut8 *buf, int count) {
	if (!fd || !fd->data || (count <= 0)) {
		return -1;
	}
	Rsrec *rih = fd->data;
	memset (buf, io->Oxff, count);
	return r_buf_read_at (rih->rbuf, io->off, buf, count);
}

static int __close(RIODesc *fd) {
	if (!fd || !fd->data) {
		return -1;
	}
	Rsrec *rih = fd->data;
	r_buf_free (rih->rbuf);
	free (rih);
	fd->data = NULL;
	return 0;
}

static ut64 __lseek(struct r_io_t *io, RIODesc *fd, ut64 offset, int whence) {
	Rsrec *rih;
	if (!fd || !fd->data) {
		return -1;
	}
	rih = fd->data;
	io->off = r_buf_seek (rih->rbuf, offset, whence);
	return io->off;
}

static bool __plugin_open(RIO *io, const char *pathname, bool many) {
	return (!strncmp (pathname, "srec://", 7));
}

//srec_parse : parse srec file loaded at *str, fill sparse buffer "rbuf"
//supported rec types : S0, S1, S2, S3
//ret 0 if ok
static bool srec_parse(RBuffer *rbuf, char *str) {
	ut8 *sec_tmp;
	ut32 sec_start = 0;	//addr for next section write
	ut32 segreg = 0;	//basis for addr fields
	ut32 addr_tmp = 0;	//addr for record
	ut16 next_addr = 0;	//for checking if records are sequential
	char *eol;
	ut8 cksum;
	int extH, extL;
	int bc = 0, type, byte, i, l;
	//fugly macro to prevent an overflow of r_buf_write_at() len
#define SEC_MAX (sec_size < INT_MAX)? sec_size: INT_MAX
	ut32 sec_size = 0;
	const int sec_count = UT16_MAX;
	sec_tmp = calloc (1, sec_count);
	if (!sec_tmp) {
		goto fail;
	}
	do {
		l = sscanf (str, "S%1x%02x", &type, &bc);
		if (l != 1) {
			eprintf ("Invalid data in srec file (%.*s)\n", 80, str);
			goto fail;
		}
		bc &= 0xff;
		type &= 0xf;

		switch (type) {
		case 0: // header
			// FIXME: Skip for now
			str = strchr (str + 1, 'S');
			break;
		case 1: // 16-bit addressed data
			eol = strchr (str + 1, 'S');
			if (eol) {
				*eol = 0;
			}
			cksum = bc;
			cksum += addr_tmp>>8;
			cksum += addr_tmp;
			cksum += type;

			if ((next_addr != addr_tmp) || ((sec_size + bc) > SEC_MAX)) {
				//previous block is not contiguous, or
				//section buffer is full => write a sparse chunk
				if (sec_size && sec_size < UT16_MAX) {
					if (r_buf_write_at (rbuf, sec_start, sec_tmp, (int) sec_size) != sec_size) {
						eprintf ("sparse buffer problem, giving up\n");
						goto fail;
					}
				}
				//advance cursor, reset section
				sec_start = segreg + addr_tmp;
				next_addr = addr_tmp;
				sec_size = 0;
			}

			for (i = 0; i < bc; i++) {
				if (sscanf (str + 9+ (i*2), "%02x", &byte) !=1) {
					eprintf ("unparsable data !\n");
					goto fail;
				}
				if (sec_size + i < sec_count) {
					sec_tmp[sec_size + i] = (ut8) byte & 0xff;
				}
				cksum += byte;
			}
			sec_size += bc;
			next_addr += bc;
			if (eol) {
				// checksum
				if (sscanf(str+9+(i*2), "%02x", &byte) !=1) {
					eprintf("unparsable data !\n");
					goto fail;
				}
				cksum += byte;
				if (cksum != 0) {
					ut8 fixedcksum = 0-(cksum-byte);
					eprintf ("Checksum failed %02x (got %02x expected %02x)\n",
						cksum, byte, fixedcksum);
					goto fail;
				}
				*eol = ':';
			}
			str = eol;
			break;
		case 2:	//extended segment record
		case 4:	//extended linear address rec
			//both rec types are handled the same except :
			//	new address = seg_reg <<4 for type 02; new address = lin_addr <<16 for type 04.
			//write current section
			if (sec_size) {
				if (r_buf_write_at(rbuf, sec_start, sec_tmp, sec_size) != sec_size) {
					eprintf("sparse buffer problem, giving up\n");
					goto fail;
				}
			}
			sec_size = 0;

			eol = strchr (str + 1, ':');
			if (eol) {
				*eol = 0;
			}
			cksum = bc;
			cksum += addr_tmp>>8;
			cksum += addr_tmp;
			cksum += type;
			if ((bc != 2) || (addr_tmp != 0)) {
				eprintf ("invalid type 02/04 record!\n");
				goto fail;
			}
			if ((sscanf (str + 9 + 0, "%02x", &extH) !=1) ||
				(sscanf (str + 9 + 2, "%02x", &extL) !=1)) {
				eprintf ("unparsable data !\n");
				goto fail;
			}
			extH &= 0xff;
			extL &= 0xff;
			cksum += extH + extL;

			segreg = extH <<8 | extL;

			//segment rec(02) gives bits 4..19; linear rec(04) is bits 16..31
			segreg = segreg << ((type==2)? 4: 16);
			next_addr = 0;
			sec_start = segreg;

			if (eol) {
				// checksum
				byte=0;	//break checksum if sscanf failed
				if (sscanf (str + 9 + 4, "%02x", &byte) != 1) {
					cksum = 1;
				}
				cksum += byte;
				if (cksum != 0) {
					ut8 fixedcksum = 0-(cksum-byte);
					eprintf ("Checksum failed %02x (got %02x expected %02x)\n",
						cksum, byte, fixedcksum);
					goto fail;
				}
				*eol = ':';
			}
			str = eol;
			break;
		case 4:	//undefined rec. Just skip.
		case 5:	//non-standard, sometimes "start linear address"
			str = strchr (str + 1, ':');
			break;
		}
	} while (str);
	free (sec_tmp);
	return true;
fail:
	free (sec_tmp);
	return false;
}

static RIODesc *__open(RIO *io, const char *pathname, int rw, int mode) {
	Rsrec *mal = NULL;
	char *str = NULL;
	if (__plugin_open (io, pathname, 0)) {
		str = r_file_slurp (pathname + 7, NULL);
		if (!str) {
			return NULL;
		}
		mal = R_NEW0 (Rsrec);
		if (!mal) {
			free (str);
			return NULL;
		}
		mal->rbuf = r_buf_new_sparse (io->Oxff);
		if (!mal->rbuf) {
			free (str);
			free (mal);
			return NULL;
		}
		if (!srec_parse (mal->rbuf, str)) {
			eprintf ("srec: failed to parse file\n");
			free (str);
			r_buf_free (mal->rbuf);
			free (mal);
			return NULL;
		}
		free (str);
		return r_io_desc_new (io, &r_io_plugin_srec,
			pathname, rw, mode, mal);
	}
	return NULL;
}

static bool __resize(RIO *io, RIODesc *fd, ut64 size) {
	if (!fd) {
		return false;
	}
	Rsrec *rih = fd->data;
	if (rih) {
		return r_buf_resize (rih->rbuf, size);
	}
	return false;
}

RIOPlugin r_io_plugin_srec = {
	.name = "srec",
	.desc = "Open Motorola S Record file",
	.uris = "srec://",
	.license = "LGPL",
	.open = __open,
	.close = __close,
	.read = __read,
	.check = __plugin_open,
	.lseek = __lseek,
	.write = __write,
	.resize = __resize
};

#ifndef R2_PLUGIN_INCORE
R_API RLibStruct radare_plugin = {
	.type = R_LIB_TYPE_IO,
	.data = &r_io_plugin_srec,
	.version = R2_VERSION
};
#endif
