/* radare - LGPL - Copyright 2013-2016 - pancake */

#include "r_util.h"
#include "r_types.h"
#include "r_parse.h"
#include "libr_tcc.h"

/* parse C code and return it in key-value form */

static void appendstring(const char *msg, char **s) {
	if (!s) {
		printf ("%s\n", msg);
	} else if (*s) {
		char *p = malloc (strlen (msg) + strlen (*s) + 1);
		if (!p) return;
		strcpy (p, *s);
		free (*s);
		*s = p;
		strcpy (p + strlen (p), msg);
	} else {
		*s = strdup (msg);
	}
}

static int typeload(void *p, const char *k, const char *v) {
	CType *ctype = (CType*)malloc(sizeof(CType));
	r_cons_printf ("tk %s=%s\n", k, v);
	//tcc_sym_push(typename, typesize, 0);
}

R_API char *r_parse_c_file(RAnal *anal, const char *path, const char* arch, int bits, const char* os) {
	char *str = NULL;
	TCCState *T = tcc_new (arch, bits, os);
	if (!T) return NULL;
	tcc_set_callback (T, &appendstring, &str);
	sdb_foreach (anal->sdb_types, typeload, NULL);
	if (tcc_add_file (T, path) == -1) {
		free (str);
		str = NULL;
	}
	tcc_delete (T);
	return str;
}

R_API char *r_parse_c_string(RAnal *anal, const char *code, const char *arch, int bits, const char* os) {
	char *str = NULL;
	TCCState *T = tcc_new (arch, bits, os);
	if (!T) return NULL;
	tcc_set_callback (T, &appendstring, &str);
	tcc_compile_string (T, code);
	tcc_delete (T);
	return str;
}

R_API int r_parse_is_c_file (const char *file) {
	const char *ext = r_str_lchr (file, '.');
	if (ext) {
		ext = ext + 1;
		if (!strcmp (ext, "cparse")
		||  !strcmp (ext, "c")
		||  !strcmp (ext, "h")) {
			return true;
		}
	}
	return false;
}
