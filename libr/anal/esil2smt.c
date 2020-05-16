/*
 * Convert from ESIL to SMTlib v2 format
 * Contributor: xvilka
 */

#include <r_anal.h>

#define EXPRBUFSZ 2048
#define REGBUFSZ 32

void smt_flag_spew_inst(RAnalEsil *esil, const char *flag);
static const char *ops[] = { FOREACHOP(SMT_OP_STRING) };

// Small SMT helpers

// Assignment
inline const char* smt2_eq(const char *a, const char *b) {
	const char *s = r_str_newf ("(= %s %s)", a, b);
	return s;
}

// Implication
inline const char* smt2_implies(const char *a, const char *b) {
	const char *s = r_str_newf ("(=> %s %s)", a, b);
	return s;
}

// Conjunction
inline const char* smt2_and(const char *a, const char *b) {
	const char *s = r_str_newf ("(and %s %s)", a, b);
	return s;
}

// Disjunction
inline const char* smt2_or(const char *a, const char *b) {
	const char *s = r_str_newf ("(or %s %s)", a, b);
	return s;
}

// If-then-else
inline const char* smt2_ite(const char *condition, const char *a, const char *b) {
	const char *s = r_str_newf ("(ite %s %s %s)", condition, a, b);
	return s;
}

// Distinction
inline const char* smt2_distinct(const char *a, const char *b) {
	const char *s = r_str_newf ("(distinct %s %s)", a, b);
	return s;
}

// Assert
inline const char* smt2_assert(const char *expression) {
	const char *s = r_str_newf ("(assert %s)", expression);
	return s;
}

// Bitvectors
inline const char* smt2_bitvec(size_t size) {
	const char *s = r_str_newf ("(_ BitVec %d)", size);
	return s;
}

inline const char* smt2_declare_bv(const char *name, size_t size) {
	const char *s = r_str_newf ("(declare-fun %s () (_ BitVec %d))", name, size);
	return s;
}

inline const char* smt2_bvval(unsigned int val, size_t size) {
	const char *s = r_str_newf ("(_ bv%u %d)", val, size);
	return s;
}

// a + b
inline const char* smt2_bvadd(const char *a, const char *b) {
	const char *s = r_str_newf ("(bvadd %s %s)", a, b);
	return s;
}
// a - b
inline const char* smt2_bvsub(const char *a, const char *b) {
	const char *s = r_str_newf ("(bvsub %s %s)", a, b);
	return s;
}
// a * b
inline const char* smt2_bvmul(const char *a, const char *b) {
	const char *s = r_str_newf ("(bvmul %s %s)", a, b);
	return s;
}
// a / b (signed)
inline const char* smt2_bvsdiv(const char *a, const char *b) {
	const char *s = r_str_newf ("(bvsdiv %s %s)", a, b);
	return s;
}
// a / b (unsigned)
inline const char* smt2_bvudiv(const char *a, const char *b) {
	const char *s = r_str_newf ("(bvudiv %s %s)", a, b);
	return s;
}
// a mod b (signed)
inline const char* smt2_bvsmod(const char *a, const char *b) {
	const char *s = r_str_newf ("(bvsmod %s %s)", a, b);
	return s;
}
// a mod b (unsigned)
inline const char* smt2_bvurem(const char *a, const char *b) {
	const char *s = r_str_newf ("(bvurem %s %s)", a, b);
	return s;
}
// a & b
inline const char* smt2_bvand(const char *a, const char *b) {
	const char *s = r_str_newf ("(bvand %s %s)", a, b);
	return s;
}
// a | b
inline const char* smt2_bvor(const char *a, const char *b) {
	const char *s = r_str_newf ("(bvor %s %s)", a, b);
	return s;
}
// a ^ b
inline const char* smt2_bvxor(const char *a, const char *b) {
	const char *s = r_str_newf ("(bvxor %s %s)", a, b);
	return s;
}
// - a
inline const char* smt2_bvneg(const char *a) {
	const char *s = r_str_newf ("(bvneg %s)", a);
	return s;
}
// a ^ b
inline const char* smt2_bvxor(const char *a, const char *b) {
	const char *s = r_str_newf ("(bvxor %s %s)", a, b);
	return s;
}
// a << b
inline const char* smt2_bvshl(const char *a, const char *b) {
	const char *s = r_str_newf ("(bvshl %s %s)", a, b);
	return s;
}
// a >> b (logical)
inline const char* smt2_bvlshr(const char *a, const char *b) {
	const char *s = r_str_newf ("(bvlshr %s %s)", a, b);
	return s;
}
// a >> b (arithmetic)
inline const char* smt2_bvashr(const char *a, const char *b) {
	const char *s = r_str_newf ("(bvashr %s %s)", a, b);
	return s;
}

// a <<< b (no direct representation)
// a << (b & (size - 1))) | (a >> (size - (b & (size - 1))))
inline const char* smt2_bvashr(const char *a, const char *b, size_t size) {
	const char *tmp0 = smt2_bvval (size, size);
	const char *tmp1 = r_str_newf ("(bvand %s (bvsub %s %s))", b, tmp0, smt2_bvval(1, size));
	const char *s = r_str_newf ("(bvor (bvlshl %s %d) (bvlshr %s (bvsub %s %s)))",
			a, tmp1, a, tmp0, tmp1)
	return s;
}
// a >>> b (no direct representation)
// a >> (b & (size - 1))) | (a << (size - (b & (size - 1))))
inline const char* smt2_bvashr(const char *a, const char *b, size_t size) {
	const char *tmp0 = smt2_bvval (size, size);
	const char *tmp1 = r_str_newf ("(bvand %s (bvsub %s %s))", b, tmp0, smt2_bvval(1, size));
	const char *s = r_str_newf ("(bvor (bvlshr %s %d) (bvlshl %s (bvsub %s %s)))",
			a, tmp1, a, tmp0, tmp1)
	return s;
}

// extract bits
inline const char* smt2_bvextract(const char *bv, unsigned int start, unsigned int end) {
	const char *s = r_str_newf ("((_ extract %d %d) %s)", end, start, bv);
	return s;
}

// concat bitvectors
inline const char* smt2_bvconcat(const char *a, const char *b) {
	const char *s = r_str_newf ("(concat %s %s)", a, b);
	return s;
}

// select bits from one bitvector to another
inline const char* smt2_bvconcat(const char *bv, unsigned int index) {
	const char *s = r_str_newf ("(select %s %d)", bv, index);
	return s;
}

// For every new expression register a new bitvector

// Get size of a register.
static ut8 esil_internal_sizeof_reg(RAnalEsil *esil, const char *r) {
	if (!esil || !esil->anal || !esil->anal->reg || !r) {
		return false;
	}
	RRegItem *i = r_reg_get(esil->anal->reg, r, -1);
	return i ? (ut8)i->size : 0;
}

RAnalSMTArgType smt_get_arg_type(RAnalEsil *esil, char *s) {
	if (!strncmp (s, smt_TEMP_PREFIX, strlen (smt_TEMP_PREFIX))) {
		return SMT_ARG_TEMP;
	}
	int type = r_anal_esil_get_parm_type(esil, s);
	switch (type) {
	case R_ANAL_ESIL_PARM_REG:
		return SMT_ARG_REG;
	case R_ANAL_ESIL_PARM_NUM:
		return SMT_ARG_CONST;
	default:
		return SMT_ARG_NONE;
	}
}

// Marshall the struct into a string
void smt_push_arg(RAnalEsil *esil, RAnalSMTArg *op) {
	// If it's not in the list of bitvectors, then add it
	const char *s = NULL;
	// Search if already in the table of declared bitvectors
	if (1) {
		// If it's already there - do nothing?
		printf("already here");
	}
	else
	{
		r_list_add(esil->smt->vectors, op);
		s = smt2_declare_bv(op->name, op->size);
		r_anal_esil_push (esil, s);
	}
}

// Unmarshall the string in stack to the struct.
RAnalSMTArg *smt_pop_arg(RAnalEsil *esil) {
	RAnalSMTArg *op;
	int i, j = 0, flag = 0, len;
	char tmp_buf[REGBUFSZ];
	char *buf = r_anal_esil_pop(esil);
	if (!buf) {
		return NULL;
	}
	len = strlen (buf);
	op = R_NEW0(RAnalSMTArg);
	for (i = 0; i < len; i++) {
		if (buf[i] == ':') {
			tmp_buf[j] = '\0';
			r_str_ncpy (op->name, tmp_buf, sizeof (op->name));
			memset (tmp_buf, 0, sizeof (tmp_buf));
			j = 0;
			flag = 1;
			continue;
		}
		// Strip all spaces
		if (buf[i] == ' ') {
			continue;
		}
		tmp_buf[j] = buf[i];
		j++;
	}
	tmp_buf[j] = '\0';

	// If we have not encountered a ':' we don't know the size yet.
	if (!flag) {
		r_str_ncpy (op->name, tmp_buf, sizeof (op->name));
		op->type = smt_get_arg_type (esil, op->name);
		if (op->type == SMT_ARG_REG) {
			op->size = esil_internal_sizeof_reg(esil, op->name);
		} else if (op->type == SMT_ARG_CONST) {
			op->size = esil->anal->bits;
		}
		free(buf);
		return op;
	}

	op->size = strtoll(tmp_buf, NULL, 10);
	op->type = smt_get_arg_type(esil, op->name);
	free(buf);
	return op;
}

// Get the next available temp register.
void get_next_temp_reg(RAnalEsil *esil, char *buf) {
	r_snprintf (buf, REGBUFSZ, smt_TEMP_PREFIX"_%02"PFMT64u,
		esil->smt->smtNextTemp);
	esil->smt->smtNextTemp++;
}

void smt_make_arg(RAnalEsil *esil, RAnalSMTArg *arg, char *name) {
	if (!arg) {
		return;
	}
	RAnalSMTArgType type = smt_get_arg_type (esil, name);
	arg->size = 0;
	arg->type = type;
	r_str_ncpy  (arg->name, name, sizeof (arg->name) - 1);
}

// Automatically increments the seq_num of the instruction.
void smt_print_expression(RAnalEsil *esil, const char* s) {
	int i;

	if (!s || !esil) {
		return;
	}
	esil->anal->cp_printf(s)
	esil->anal->cb_printf("\n");
}

// Used to cast sizes during assignment. OR is used for casting.
// Pushes the new *casted* src onto stack. Warning: Frees the original src!
void smt_cast_size(RAnalEsil *esil, RAnalSMTArg *src, RAnalSMTArg *dst) {
	char tmp_buf[REGBUFSZ];
	RAnalsmtInst *ins;

	if (!src || !dst) {
		return;
	}
	// No need to case sizes if dst and src are of same size.
	if (src->size == dst->size) {
		smt_push_arg(esil, src);
		return;
	}
	snprintf (tmp_buf, REGBUFSZ-1, "0:%d", dst->size);
	r_anal_esil_push (esil, tmp_buf);
	RAnalSMTArg *arg1 = smt_pop_arg (esil);
	RAnalSMTArg *arg2 = R_NEW0(RAnalSMTArg);
	get_next_temp_reg (esil, tmp_buf);
	smt_make_arg (esil, arg2, tmp_buf);
	if (arg2) {
		arg2->size = dst->size;
	}
	smt_print_expression (esil, ins);
	if (arg2) {
		smt_push_arg (esil, arg2);
	}
	free(arg1);
	free(arg2);
}

// Here start translation functions!
static bool smt_eq(RAnalEsil *esil) {
	char tmp_buf[REGBUFSZ];
	RAnalSMTArgType src_type, dst_type;
	RAnalSMTArg *dst, *src;

	dst = smt_pop_arg (esil);
	if (!dst) {
		return false;
	}
	src = smt_pop_arg (esil);
	if (!src) {
		R_FREE (dst);
		return false;
	}

	src_type = src->type;
	// Check if the src is an internal var. If it is, we need to resolve it.
	if (src_type == SMT_ARG_ESIL_INTERNAL) {
		smt_flag_spew_inst (esil, src->name + 1);
		R_FREE (src);
		src = smt_pop_arg (esil);
	} else if (src_type == SMT_ARG_REG) {
		RAnalSMTArg *arg1 = R_NEW(RAnalSMTArg);
		smt_make_arg (esil, arg1, " ");
		get_next_temp_reg (esil, tmp_buf);
		RAnalSMTArg *arg2 = R_NEW(RAnalSMTArg);
		smt_make_arg (esil, arg2, tmp_buf);
		arg2->size = arg0->size;
		s = smt2_eq (arg1->name, arg2->name);
		smt_print_expression (esil, s);
		smt_push_arg (esil, arg2);
		src = smt_pop_arg (esil);
		free(arg1);
		free(arg2);
	}


	char* expression = malloc(EXPRBUFSZ);
	r_snprintf (expression, sizeof (EXPRBUFSZ) - 1, "(= %s %s)")
	smt_make_arg (esil, ins->arg[1], " ");
	smt_print_expression (esil, ins);
	return true;
}

static int smt_and(RAnalEsil *esil) {
	ut8 dst_size;
	RAnalSMTArg *op2, *op1;

	op2 = smt_pop_arg (esil);
	if (!op2) {
		return false;
	}
	op1 = smt_pop_arg (esil);
	if (!op1) {
		R_FREE (op2);
		return false;
	}
	char *s = smt2_bvand (op1, op2);
	smt_print_expression (esil, s);
	return true;
}

static int smt_or(RAnalEsil *esil) {
	ut8 dst_size;
	RAnalSMTArg *op2, *op1;

	op2 = smt_pop_arg (esil);
	if (!op2) {
		return false;
	}
	op1 = smt_pop_arg (esil);
	if (!op1) {
		R_FREE (op2);
		return false;
	}
	char *s = smt2_bvor (op1, op2);
	smt_print_expression (esil, s);
	return true;
}

static int smt_xor(RAnalEsil *esil) {
	ut8 dst_size;
	RAnalSMTArg *op2, *op1;

	op2 = smt_pop_arg (esil);
	if (!op2) {
		return false;
	}
	op1 = smt_pop_arg (esil);
	if (!op1) {
		R_FREE (op2);
		return false;
	}
	char *s = smt2_bvxor (op1, op2);
	smt_print_expression (esil, s);
	return true;
}

static int smt_lsl(RAnalEsil *esil) {
	ut8 dst_size;
	RAnalSMTArg *op2, *op1;

	op2 = smt_pop_arg (esil);
	if (!op2) {
		return false;
	}
	op1 = smt_pop_arg (esil);
	if (!op1) {
		R_FREE (op2);
		return false;
	}
	char *s = smt2_bvlsl (op1, op2);
	smt_print_expression (esil, s);
	return true;
}

static int smt_lsr(RAnalEsil *esil) {
	ut8 dst_size;
	RAnalSMTArg *op2, *op1;

	op2 = smt_pop_arg (esil);
	if (!op2) {
		return false;
	}
	op1 = smt_pop_arg (esil);
	if (!op1) {
		R_FREE (op2);
		return false;
	}
	char *s = smt2_bvlsr (op1, op2);
	smt_print_expression (esil, s);
	return true;
}

static int smt_andeq(RAnalEsil *esil) {
	int ret = 1;
	RAnalSMTArg *op = smt_pop_arg(esil);
	if (!op) {
		return false;
	}

	smt_push_arg(esil, op);
	ret &= smt_and(esil, opcode);
	smt_push_arg(esil, op);
	ret &= smt_eq(esil);
	R_FREE(op);
	return ret;
}

static int smt_oreq(RAnalEsil *esil) {
	int ret = 1;
	RAnalSMTArg *op = smt_pop_arg(esil);
	if (!op) {
		return false;
	}

	smt_push_arg(esil, op);
	ret &= smt_or(esil, opcode);
	smt_push_arg(esil, op);
	ret &= smt_eq(esil);
	R_FREE(op);
	return ret;
}

static int smt_xoreq(RAnalEsil *esil) {
	int ret = 1;
	RAnalSMTArg *op = smt_pop_arg(esil);
	if (!op) {
		return false;
	}

	smt_push_arg(esil, op);
	ret &= smt_xor(esil, opcode);
	smt_push_arg(esil, op);
	ret &= smt_eq(esil);
	R_FREE(op);
	return ret;
}

static bool smt_cmp(RAnalEsil *esil) {
	RAnalsmtInst *ins;
	char tmp_buf[REGBUFSZ];
	RAnalSMTArg *op2, *op1;

	op2 = smt_pop_arg (esil);
	if (!op2) {
		return false;
	}
	op1 = smt_pop_arg (esil);
	if (!op1) {
		R_FREE (op2);
		return false;
	}

	ins = R_NEW0 (RAnalsmtInst);
	if (!ins) {
		R_FREE (op1);
		R_FREE (op2);
		return false;
	}
	ins->opcode = smt_EQ;
	ins->arg[0] = op2;
	ins->arg[1] = op1;
	ins->arg[2] = R_NEW0 (RAnalSMTArg);
	if (!ins->arg[2]) {
		smt_free_inst (ins);
		return false;
	}
	get_next_temp_reg (esil, tmp_buf);
	smt_make_arg (esil, ins->arg[2], tmp_buf);
	ins->arg[2]->size = 1;
	smt_print_expression (esil, ins);
	// Set vars needed to determine flags.
	r_snprintf (esil->smt->cur, sizeof (esil->smt->old) - 1, "%s:%d",
			ins->arg[2]->name, ins->arg[2]->size);
	r_snprintf (esil->smt->old, sizeof (esil->smt->cur) - 1, "%s:%d",
			op2->name, op2->size);
	if (r_reg_get (esil->anal->reg, op2->name, -1)) {
		esil->smt->lastsz = op2->size;
	} else if (r_reg_get (esil->anal->reg, op1->name, -1)) {
		esil->smt->lastsz = op1->size;
	}
	smt_push_arg (esil, ins->arg[2]);
	smt_free_inst (ins);
	return true;
}

static bool smt_smaller_equal(RAnalEsil *esil) {
	RAnalSMTArg *op2, *op1;

	op2 = smt_pop_arg(esil);
	if (!op2) {
		return false;
	}
	op1 = smt_pop_arg(esil);
	if (!op1) {
		R_FREE (op2);
		return false;
	}

	smt_push_arg(esil, op1);
	smt_push_arg(esil, op2);
	smt_smaller(esil);
	smt_push_arg(esil, op1);
	smt_push_arg(esil, op2);
	smt_cmp(esil);
	smt_or(esil);

	R_FREE(op1);
	R_FREE(op2);
	return true;
}

static bool smt_larger(RAnalEsil *esil) {
	RAnalSMTArg *op2 = smt_pop_arg(esil);
	if (!op2) {
		return false;
	}
	RAnalSMTArg *op1 = smt_pop_arg(esil);
	if (!op1) {
		R_FREE (op2);
		return false;
	}
	smt_push_arg (esil, op2);
	smt_push_arg (esil, op1);
	smt_smaller (esil);
	R_FREE (op1);
	R_FREE (op2);
	return true;
}

static bool smt_larger_equal(RAnalEsil *esil) {
	RAnalSMTArg *op2, *op1;

	op2 = smt_pop_arg(esil);
	if (!op2) {
		return false;
	}
	op1 = smt_pop_arg(esil);
	if (!op1) {
		R_FREE (op2);
		return false;
	}

	smt_push_arg (esil, op2);
	smt_push_arg (esil, op1);
	smt_smaller_equal (esil);
	R_FREE (op1);
	R_FREE (op2);
	return true;
}

static bool smt_dec(RAnalEsil *esil) {
	RAnalSMTArg *op = smt_pop_arg(esil);
	if (!op) {
		return false;
	}
	r_anal_esil_pushnum (esil, 1);
	smt_push_arg (esil, op);
	smt_sub (esil);
	R_FREE (op);
	return true;
}

static bool smt_deceq(RAnalEsil *esil) {
	RAnalSMTArg *op1 = smt_pop_arg(esil);
	if (!op1) {
		return false;
	}
	smt_push_arg (esil, op1);
	smt_dec (esil);
	smt_push_arg (esil, op1);
	smt_eq (esil);
	R_FREE (op1);
	return true;
}

static bool smt_inc(RAnalEsil *esil) {
	RAnalSMTArg *op = smt_pop_arg(esil);
	if (!op) {
		return false;
	}

	r_anal_esil_pushnum(esil, 1);
	smt_push_arg(esil, op);
	smt_add(esil);
	R_FREE(op);
	return true;
}

static bool smt_inceq(RAnalEsil *esil) {
	RAnalSMTArg *op = smt_pop_arg(esil);
	if (!op) {
		return false;
	}
	smt_push_arg (esil, op);
	smt_inc (esil);
	smt_push_arg (esil, op);
	smt_eq (esil);
	R_FREE (op);
	return true;
}

static bool smt_neg(RAnalEsil *esil) {
	char tmp_buf[REGBUFSZ];
	RAnalsmtInst *ins;
	RAnalSMTArg *op = smt_pop_arg (esil);
	if (!op) {
		return false;
	}
	ins = R_NEW0 (RAnalsmtInst);
	if (!ins) {
		R_FREE (op);
		return false;
	}
	ins->opcode = smt_EQ;
	ins->arg[0] = op;
	r_anal_esil_pushnum (esil, 0);
	ins->arg[1] = smt_pop_arg(esil);
	if (!ins->arg[1]) {
		smt_free_inst (ins);
		return false;
	}
	ins->arg[2] = R_NEW0 (RAnalSMTArg);
	if (!ins->arg[2]) {
		smt_free_inst (ins);
		return false;
	}
	get_next_temp_reg (esil, tmp_buf);
	smt_make_arg(esil, ins->arg[2], tmp_buf);
	if (ins->arg[0]->size < ins->arg[1]->size) {
		ins->arg[1]->size = ins->arg[0]->size;
	}

	ins->arg[2]->size = 1;
	smt_print_expression (esil, ins);
	smt_push_arg (esil, ins->arg[2]);
	smt_free_inst (ins);
	return true;
}

static bool smt_negeq(RAnalEsil *esil) {
	RAnalSMTArg *op = smt_pop_arg(esil);
	if (!op) {
		return false;
	}
	smt_push_arg (esil, op);
	smt_neg (esil);
	smt_push_arg (esil, op);
	smt_eq (esil);
	free (op);
	return true;
}

static bool smt_not(RAnalEsil *esil) {
	char tmp_buf[REGBUFSZ];
	RAnalsmtInst *ins;
	RAnalSMTArg *op = smt_pop_arg (esil);
	if (!op) {
		return false;
	}

	ins = R_NEW0 (RAnalsmtInst);
	if (!ins) {
		R_FREE (op);
		return false;
	}
	ins->opcode = smt_NOT;
	ins->arg[0] = op;
	ins->arg[1] = R_NEW0 (RAnalSMTArg);
	if (!ins->arg[1]) {
		smt_free_inst (ins);
		return false;
	}
	ins->arg[2] = R_NEW0 (RAnalSMTArg);
	if (!ins->arg[2]) {
		smt_free_inst (ins);
		return false;
	}
	smt_make_arg (esil, ins->arg[1], " ");
	get_next_temp_reg (esil, tmp_buf);
	smt_make_arg (esil, ins->arg[2], tmp_buf);
	ins->arg[2]->size = ins->arg[0]->size;
	smt_print_expression (esil, ins);
	smt_push_arg (esil, ins->arg[2]);
	smt_free_inst (ins);
	return true;
}

static bool smt_if(RAnalEsil *esil) {
	RAnalsmtInst *ins;
	RAnalSMTArg *op2, *op1;

	op2 = smt_pop_arg (esil);
	if (!op2) {
		return false;
	}
	op1 = smt_pop_arg (esil);
	if (!op1) {
		R_FREE (op2);
		return false;
	}

	smt2_ite(cond, op1, op2)
	ins->arg[0] = op1;
	ins->arg[2] = op2;
	ins->arg[1] = R_NEW0 (RAnalSMTArg);
	if (!ins->arg[1]) {
		smt_free_inst (ins);
		return false;
	}
	smt_make_arg (esil, ins->arg[1], " ");
	smt_print_expression (esil, ins);
	smt_free_inst (ins);
	return true;
}

static bool smt_if_end(RAnalEsil *esil) { return true; }

static bool smt_peek(RAnalEsil *esil) {
	RAnalsmtInst *ins;
	char tmp_buf[REGBUFSZ];
	RAnalSMTArg *op1 = smt_pop_arg(esil);
	if (!op1) {
		return false;
	}

	ins = R_NEW0 (RAnalsmtInst);
	if (!ins) {
		R_FREE (op1);
		return false;
	}
	ins->opcode = smt_LDM;
	ins->arg[0] = op1;
	ins->arg[1] = R_NEW0(RAnalSMTArg);
	if (!ins->arg[1]) {
		smt_free_inst (ins);
		return false;
	}
	ins->arg[2] = R_NEW0(RAnalSMTArg);
	if (!ins->arg[2]) {
		smt_free_inst (ins);
		return false;
	}
	smt_make_arg(esil, ins->arg[1], " ");
	get_next_temp_reg(esil, tmp_buf);
	smt_make_arg(esil, ins->arg[2], tmp_buf);
	ins->arg[2]->size = ins->arg[0]->size;
	smt_print_expression(esil, ins);
	smt_push_arg(esil, ins->arg[2]);
	smt_free_inst(ins);
	return true;
}

// n = 8, 4, 2, 1
static bool smt_peekn(RAnalEsil *esil, ut8 n) {
	RAnalSMTArg *op2;
	RAnalSMTArg *op1 = smt_pop_arg (esil);
	if (!op1) {
		return false;
	}

	smt_push_arg (esil, op1);
	smt_peek (esil);
	// No need to cast if n = 0
	if (n == 0) {
		R_FREE (op1);
		return true;
	}

	R_FREE (op1);
	op1 = smt_pop_arg (esil);
	if (!op1) {
		return false;
	}

	op2 = R_NEW0 (RAnalSMTArg);
	if (!op2) {
		R_FREE (op1);
		return false;
	}
	op2->size = n * 8;
	op2->type = SMT_ARG_TEMP;
	get_next_temp_reg (esil, op2->name);
	smt_cast_size (esil, op1, op2);
	esil->smt->lastsz = 8 * n;

	R_FREE (op2);
	return true;
}

static bool smt_peek1(RAnalEsil *esil) { return smt_peekn(esil, 1); }
static bool smt_peek2(RAnalEsil *esil) { return smt_peekn(esil, 2); }
static bool smt_peek4(RAnalEsil *esil) { return smt_peekn(esil, 4); }
static bool smt_peek8(RAnalEsil *esil) { return smt_peekn(esil, 8); }

// n = 8, 4, 2, 1
static bool smt_poken(RAnalEsil *esil, ut8 n) {
	char tmp_buf[REGBUFSZ];
	RAnalsmtInst *ins;
	RAnalSMTArg *op2, *op1;

	op2 = smt_pop_arg (esil);
	if (!op2) {
		return false;
	}
	op1 = smt_pop_arg (esil);
	if (!op1) {
		R_FREE (op2);
		return false;
	}

	if (op1->type != SMT_ARG_ESIL_INTERNAL) {
		ins = R_NEW0 (RAnalsmtInst);
		if (!ins) {
			R_FREE (op2);
			R_FREE (op1);
			return false;
		}
		ins->opcode = smt_LDM;
		ins->arg[0] = op2;
		ins->arg[1] = R_NEW0(RAnalSMTArg);
		if (!ins->arg[1]) {
			R_FREE (op1);
			smt_free_inst (ins);
			return false;
		}
		ins->arg[2] = R_NEW0(RAnalSMTArg);
		if (!ins->arg[2]) {
			R_FREE (op1);
			smt_free_inst (ins);
			return false;
		}
		smt_make_arg (esil, ins->arg[1], " ");
		get_next_temp_reg (esil, tmp_buf);
		smt_make_arg (esil, ins->arg[2], tmp_buf);
		ins->arg[2]->size = ins->arg[0]->size;
		smt_print_expression (esil, ins);
		r_snprintf (esil->smt->old, sizeof (esil->smt->old) - 1, "%s:%d",
				ins->arg[2]->name, ins->arg[2]->size);
		r_snprintf (esil->smt->cur, sizeof (esil->smt->cur) - 1, "%s:%d",
				op2->name, op2->size);
		esil->lastsz = n * 8;
		smt_push_arg (esil, op1);
		smt_push_arg (esil, op2);
		R_FREE (op1);
		smt_free_inst (ins);
	} else {
		smt_flag_spew_inst (esil, op1->name + 1);
		R_FREE (op1);
		op1 = smt_pop_arg (esil);
		smt_push_arg (esil, op2);
		smt_push_arg (esil, op1);
		R_FREE (op2);
		R_FREE (op1);
	}

	ins = R_NEW0 (RAnalsmtInst);
	if (!ins) {
		return false;
	}
	ins->opcode = smt_STM;
	ins->arg[2] = smt_pop_arg (esil);
	ins->arg[0] = smt_pop_arg (esil);
	ins->arg[1] = R_NEW0 (RAnalSMTArg);
	if (!ins->arg[1]) {
		smt_free_inst (ins);
		return false;
	}
	smt_make_arg(esil, ins->arg[1], " ");
	smt_print_expression(esil, ins);
	return true;
}

static bool smt_poke(RAnalEsil *esil) {
	return smt_poken (esil, esil->anal->bits / 8);
}

static bool smt_poke1(RAnalEsil *esil) { return smt_poken(esil, 1); }
static bool smt_poke2(RAnalEsil *esil) { return smt_poken(esil, 2); }
static bool smt_poke4(RAnalEsil *esil) { return smt_poken(esil, 4); }
static bool smt_poke8(RAnalEsil *esil) { return smt_poken(esil, 8); }

// Generic function to handle all mem_*eq_n functions. Example, mem_oreq_n
static bool smt_mem_bineq_n(RAnalEsil *esil, RAnalsmtOpcode opcode, ut8 size) {
	int ret = 1;
	RAnalSMTArg *op2, *op1;

	op2 = smt_pop_arg (esil);
	if (!op2) {
		return false;
	}
	op1 = smt_pop_arg (esil);
	if (!op1) {
		R_FREE (op2);
		return false;
	}

	smt_push_arg(esil, op2);
	ret &= smt_peekn(esil, size);
	smt_push_arg(esil, op1);
	ret &= smt_binop(esil, opcode);
	smt_push_arg(esil, op2);
	ret &= smt_poken(esil, size);

	free (op2);
	free (op1);
	return ret;
}

static bool smt_mem_oreq(RAnalEsil *esil)  { return smt_mem_bineq_n(esil, smt_OR, esil->anal->bits / 8); }
static bool smt_mem_oreq1(RAnalEsil *esil) { return smt_mem_bineq_n(esil, smt_OR, 1); }
static bool smt_mem_oreq2(RAnalEsil *esil) { return smt_mem_bineq_n(esil, smt_OR, 2); }
static bool smt_mem_oreq4(RAnalEsil *esil) { return smt_mem_bineq_n(esil, smt_OR, 4); }
static bool smt_mem_oreq8(RAnalEsil *esil) { return smt_mem_bineq_n(esil, smt_OR, 8); }

static bool smt_mem_andeq(RAnalEsil *esil)  { return smt_mem_bineq_n(esil, smt_AND, esil->anal->bits / 8); }
static bool smt_mem_andeq1(RAnalEsil *esil) { return smt_mem_bineq_n(esil, smt_AND, 1); }
static bool smt_mem_andeq2(RAnalEsil *esil) { return smt_mem_bineq_n(esil, smt_AND, 2); }
static bool smt_mem_andeq4(RAnalEsil *esil) { return smt_mem_bineq_n(esil, smt_AND, 4); }
static bool smt_mem_andeq8(RAnalEsil *esil) { return smt_mem_bineq_n(esil, smt_AND, 8); }

static bool smt_mem_xoreq(RAnalEsil *esil)  { return smt_mem_bineq_n(esil, smt_XOR, esil->anal->bits / 8); }
static bool smt_mem_xoreq1(RAnalEsil *esil) { return smt_mem_bineq_n(esil, smt_XOR, 1); }
static bool smt_mem_xoreq2(RAnalEsil *esil) { return smt_mem_bineq_n(esil, smt_XOR, 2); }
static bool smt_mem_xoreq4(RAnalEsil *esil) { return smt_mem_bineq_n(esil, smt_XOR, 4); }
static bool smt_mem_xoreq8(RAnalEsil *esil) { return smt_mem_bineq_n(esil, smt_XOR, 8); }

static bool smt_mem_addeq(RAnalEsil *esil)  { return smt_mem_bineq_n(esil, smt_ADD, esil->anal->bits / 8); }
static bool smt_mem_addeq1(RAnalEsil *esil) { return smt_mem_bineq_n(esil, smt_ADD, 1); }
static bool smt_mem_addeq2(RAnalEsil *esil) { return smt_mem_bineq_n(esil, smt_ADD, 2); }
static bool smt_mem_addeq4(RAnalEsil *esil) { return smt_mem_bineq_n(esil, smt_ADD, 4); }
static bool smt_mem_addeq8(RAnalEsil *esil) { return smt_mem_bineq_n(esil, smt_ADD, 8); }

static bool smt_mem_subeq(RAnalEsil *esil)  { return smt_mem_bineq_n(esil, smt_SUB, esil->anal->bits / 8); }
static bool smt_mem_subeq1(RAnalEsil *esil) { return smt_mem_bineq_n(esil, smt_SUB, 1); }
static bool smt_mem_subeq2(RAnalEsil *esil) { return smt_mem_bineq_n(esil, smt_SUB, 2); }
static bool smt_mem_subeq4(RAnalEsil *esil) { return smt_mem_bineq_n(esil, smt_SUB, 4); }
static bool smt_mem_subeq8(RAnalEsil *esil) { return smt_mem_bineq_n(esil, smt_SUB, 8); }

static bool smt_mem_muleq(RAnalEsil *esil)  { return smt_mem_bineq_n(esil, smt_MUL, esil->anal->bits / 8); }
static bool smt_mem_muleq1(RAnalEsil *esil) { return smt_mem_bineq_n(esil, smt_MUL, 1); }
static bool smt_mem_muleq2(RAnalEsil *esil) { return smt_mem_bineq_n(esil, smt_MUL, 2); }
static bool smt_mem_muleq4(RAnalEsil *esil) { return smt_mem_bineq_n(esil, smt_MUL, 4); }
static bool smt_mem_muleq8(RAnalEsil *esil) { return smt_mem_bineq_n(esil, smt_MUL, 8); }

static bool smt_mem_inceq_n(RAnalEsil *esil, ut8 size) {
	int ret = 1;
	RAnalSMTArg *op1 = smt_pop_arg(esil);
	if (!op1) {
		return false;
	}

	r_anal_esil_pushnum(esil, 1);
	smt_push_arg(esil, op1);
	ret &= smt_mem_bineq_n(esil, smt_ADD, size);

	free (op1);
	return ret;
}

static bool smt_mem_inceq(RAnalEsil *esil) {
	return smt_mem_inceq_n(esil, esil->anal->bits / 8);
}
static bool smt_mem_inceq1(RAnalEsil *esil) { return smt_mem_inceq_n(esil, 1); }
static bool smt_mem_inceq2(RAnalEsil *esil) { return smt_mem_inceq_n(esil, 2); }
static bool smt_mem_inceq4(RAnalEsil *esil) { return smt_mem_inceq_n(esil, 4); }
static bool smt_mem_inceq8(RAnalEsil *esil) { return smt_mem_inceq_n(esil, 8); }

static int smt_mem_deceq_n(RAnalEsil *esil, ut8 size) {
	int ret = 1;
	RAnalSMTArg *op1 = smt_pop_arg(esil);
	if (!op1) {
		return false;
	}

	r_anal_esil_pushnum(esil, 1);
	smt_push_arg(esil, op1);
	ret &= smt_mem_bineq_n(esil, smt_SUB, size);

	free (op1);
	return ret;
}

static bool smt_mem_deceq(RAnalEsil *esil) {
	return smt_mem_deceq_n(esil, esil->anal->bits / 8);
}
static bool smt_mem_deceq1(RAnalEsil *esil) { return smt_mem_deceq_n(esil, 1); }
static bool smt_mem_deceq2(RAnalEsil *esil) { return smt_mem_deceq_n(esil, 2); }
static bool smt_mem_deceq4(RAnalEsil *esil) { return smt_mem_deceq_n(esil, 4); }
static bool smt_mem_deceq8(RAnalEsil *esil) { return smt_mem_deceq_n(esil, 8); }

// Functions to resolve internal vars.
// performs (2 << op) - 1
void smt_generate_mask(RAnalEsil *esil) {
	r_anal_esil_pushnum(esil, 2);
	smt_lsl(esil);
	smt_dec(esil);
}

void smt_generate_borrow_flag(RAnalEsil *esil, ut8 bit) {
	RAnalSMTArg *op1;

	r_anal_esil_pushnum(esil, bit);
	r_anal_esil_pushnum(esil, 0x3f);
	smt_and(esil);
	r_anal_esil_pushnum(esil, 0x3f);
	smt_add(esil);
	r_anal_esil_pushnum(esil, 0x3f);
	smt_and(esil);
	// Generate the mask. 2 << bits - 1
	smt_generate_mask(esil);
	op1 = smt_pop_arg(esil);
	// old & mask
	r_anal_esil_push(esil, esil->smt->old);
	smt_push_arg(esil, op1);
	smt_and(esil);
	// cur & mask
	r_anal_esil_push(esil, esil->smt->cur);
	smt_push_arg(esil, op1);
	smt_and(esil);
	// Check
	smt_larger(esil);

	free (op1);
}

void smt_generate_carry_flag(RAnalEsil *esil, ut8 bit) {
	RAnalSMTArg *op1;

	r_anal_esil_pushnum(esil, bit);
	r_anal_esil_pushnum(esil, 0x3f);
	smt_and(esil);
	// Generate the mask. 2 << bits - 1
	smt_generate_mask(esil);
	op1 = smt_pop_arg(esil);
	// old & mask
	r_anal_esil_push(esil, esil->smt->old);
	smt_push_arg(esil, op1);
	smt_and(esil);
	// cur & mask
	r_anal_esil_push(esil, esil->smt->cur);
	smt_push_arg(esil, op1);
	smt_and(esil);
	// Check
	smt_smaller(esil);

	free (op1);
}

void smt_generate_partity_flag(RAnalEsil *esil) {
	// Generation of parity flag taken from opensmt README example.
	RAnalSMTArg *op;
	r_anal_esil_push(esil, esil->smt->cur);
	r_anal_esil_pushnum(esil, 0xff);
	smt_and(esil);
	op = smt_pop_arg(esil);
	if (!op) {
		return;
	}

	r_anal_esil_pushnum(esil, 7);
	smt_push_arg(esil, op);
	smt_lsr(esil);
	r_anal_esil_pushnum(esil, 6);
	smt_push_arg(esil, op);
	smt_lsr(esil);
	smt_xor(esil);
	r_anal_esil_pushnum(esil, 5);
	smt_push_arg(esil, op);
	smt_lsr(esil);
	r_anal_esil_pushnum(esil, 4);
	smt_push_arg(esil, op);
	smt_lsr(esil);
	smt_xor(esil);
	smt_xor(esil);
	r_anal_esil_pushnum(esil, 3);
	smt_push_arg(esil, op);
	smt_lsr(esil);
	r_anal_esil_pushnum(esil, 2);
	smt_push_arg(esil, op);
	smt_lsr(esil);
	smt_xor(esil);
	r_anal_esil_pushnum(esil, 1);
	smt_push_arg(esil, op);
	smt_lsr(esil);
	smt_push_arg(esil, op);
	smt_xor(esil);
	smt_xor(esil);
	smt_xor(esil);
	r_anal_esil_pushnum(esil, 1);
	smt_and(esil);
	smt_not(esil);

	free (op);
}

void smt_generate_signature(RAnalEsil *esil) {
	if (!esil->smt->lastsz || esil->smt->lastsz == 0) {
		r_anal_esil_pushnum(esil, 0);
		return;
	}

	RAnalSMTArg *op;

	r_anal_esil_pushnum(esil, esil->smt->lastsz - 1);
	r_anal_esil_pushnum(esil, 1);
	smt_lsl(esil);
	r_anal_esil_push(esil, esil->smt->cur);
	smt_and(esil);

	op = smt_pop_arg(esil);
	if (!op) {
		return;
	}

	r_anal_esil_pushnum(esil, esil->smt->lastsz - 1);
	smt_push_arg(esil, op);
	smt_lsr(esil);

	free (op);
}

void smt_generate_overflow_flag(RAnalEsil *esil) {
	if (esil->smt->lastsz < 2) {
		r_anal_esil_pushnum (esil, 0);
	}

	smt_generate_borrow_flag(esil, esil->smt->lastsz);
	smt_generate_carry_flag(esil, esil->smt->lastsz - 2);
	smt_xor(esil);
}

void smt_flag_spew_inst(RAnalEsil *esil, const char *flag) {
	ut8 bit;
	switch (flag[0]) {
		case 'z': // zero-flag
			r_anal_esil_push(esil, esil->smt->cur);
			break;
		case 'b':
			bit = (ut8)r_num_get(NULL, &flag[1]);
			smt_generate_borrow_flag(esil, bit);
			break;
		case 'c':
			bit = (ut8)r_num_get(NULL, &flag[1]);
			smt_generate_carry_flag(esil, bit);
			break;
		case 'o':
			smt_generate_overflow_flag(esil);
			break;
		case 'p':
			smt_generate_partity_flag(esil);
			break;
		case 'r':
			r_anal_esil_pushnum(esil, esil->anal->bits / 8);
			break;
		case 's':
			smt_generate_signature(esil);
			break;
		default:
			return;
	}

	return;
}

/* Callback hook for command_hook */
static int setup_smt_ins(RAnalEsil *esil, const char *op) {
	esil->smt->addr++;      // Increment the address location.
	return 0;
}

R_API int r_anal_esil_to_smt_setup(RAnalEsil *esil, RAnal *anal, int romem,
		int stats) {
	if (!esil) {
		return false;
	}
	esil->verbose = 2;
	esil->anal = anal;
	esil->trap = 0;
	esil->trap_code = 0;

	/* Set up a callback for hook_command */
	esil->cb.hook_command = setup_smt_ins;

	esil->smt = R_NEW0(RAnalSMT);
	if (!esil->smt) {
		return false;
	}
	esil->smt->addr = -1;
	esil->smt->skip = 0;
	esil->smt->logic = "(set-logic QF_ABV)";
	// We also should add "(check-sat)" at the end
	// Also we have to think on how to extract models in
	// the way that r2 can consume

	// Store the pc
	const char *name = r_reg_get_name (esil->anal->reg, r_reg_get_name_idx ("PC"));
	strncpy (esil->smt->pc, name, sizeof (esil->smt->pc) - 1);

	r_anal_esil_mem_ro(esil, romem);

#define	OT_UNK	R_ANAL_ESIL_OP_TYPE_UNKNOWN
#define	OT_CTR	R_ANAL_ESIL_OP_TYPE_CONTROL_FLOW
#define	OT_MATH	R_ANAL_ESIL_OP_TYPE_MATH
#define	OT_REGW	R_ANAL_ESIL_OP_TYPE_REG_WRITE
#define	OT_MEMW	R_ANAL_ESIL_OP_TYPE_MEM_WRITE
#define	OT_MEMR	R_ANAL_ESIL_OP_TYPE_MEM_READ

	r_anal_esil_set_op(esil, "=", smt_eq, 0, 2, OT_REGW);
	r_anal_esil_set_op(esil, ":=", smt_eq, 0, 2, OT_REGW);
	r_anal_esil_set_op(esil, "+", smt_add, 1, 2, OT_MATH);
	r_anal_esil_set_op(esil, "+=", smt_addeq, 0, 2, OT_MATH | OT_REGW);
	r_anal_esil_set_op(esil, "-", smt_sub, 1, 2, OT_MATH);
	r_anal_esil_set_op(esil, "-=", smt_subeq, 0, 2, OT_MATH | OT_REGW);
	r_anal_esil_set_op(esil, "*", smt_mul, 1, 2, OT_MATH);
	r_anal_esil_set_op(esil, "*=", smt_muleq, 0, 2, OT_MATH | OT_REGW);
	r_anal_esil_set_op(esil, "/", smt_div, 1, 2, OT_MATH);
	r_anal_esil_set_op(esil, "/=", smt_diveq, 0, 2, OT_MATH | OT_REGW);
	r_anal_esil_set_op(esil, "^", smt_xor, 1, 2, OT_MATH);
	r_anal_esil_set_op(esil, "^=", smt_xoreq, 0, 2, OT_MATH | OT_REGW);
	r_anal_esil_set_op(esil, "|", smt_or, 1, 2, OT_MATH);
	r_anal_esil_set_op(esil, "|=", smt_oreq, 0, 2, OT_MATH | OT_REGW);
	r_anal_esil_set_op(esil, "&", smt_and, 1, 2, OT_MATH);
	r_anal_esil_set_op(esil, "&=", smt_andeq, 0, 2, OT_MATH | OT_REGW);
	r_anal_esil_set_op(esil, "<<", smt_lsl, 1, 2, OT_MATH);
	r_anal_esil_set_op(esil, "<<=", smt_lsleq, 0, 2, OT_MATH | OT_REGW);
	r_anal_esil_set_op(esil, ">>", smt_lsr, 1, 2, OT_MATH);
	r_anal_esil_set_op(esil, ">>=", smt_lsreq, 0, 2, OT_MATH | OT_REGW);
	r_anal_esil_set_op(esil, "++=", smt_inceq, 0, 1, OT_MATH | OT_REGW);
	r_anal_esil_set_op(esil, "++", smt_inc, 1, 1, OT_MATH);
	r_anal_esil_set_op(esil, "--=", smt_deceq, 0, 1, OT_MATH | OT_REGW);
	r_anal_esil_set_op(esil, "--", smt_dec, 1, 1, OT_MATH);
	r_anal_esil_set_op(esil, "!", smt_neg, 1, 1, OT_MATH);
	r_anal_esil_set_op(esil, "!=", smt_negeq, 0, 1, OT_MATH);
	r_anal_esil_set_op(esil, "==", smt_cmp, 0, 2, OT_MATH);
	r_anal_esil_set_op(esil, "<", smt_smaller, 1, 2, OT_MATH);
	r_anal_esil_set_op(esil, ">", smt_larger, 1, 2, OT_MATH);
	r_anal_esil_set_op(esil, "<=", smt_smaller_equal, 1, 2, OT_MATH);
	r_anal_esil_set_op(esil, ">=", smt_larger_equal, 1, 2, OT_MATH);
	r_anal_esil_set_op(esil, "[]", smt_peek, 1, 1, OT_MEMR);
	r_anal_esil_set_op(esil, "=[]", smt_poke, 0, 2, OT_MEMW);
	r_anal_esil_set_op(esil, "|=[]", smt_mem_oreq, 0, 2, OT_MATH | OT_MEMR | OT_MEMW);
	r_anal_esil_set_op(esil, "^=[]", smt_mem_xoreq, 0, 2, OT_MATH | OT_MEMR | OT_MEMW);
	r_anal_esil_set_op(esil, "&=[]", smt_mem_andeq, 0, 2, OT_MATH | OT_MEMR | OT_MEMW);
	r_anal_esil_set_op(esil, "+=[]", smt_mem_addeq, 0, 2, OT_MATH | OT_MEMR | OT_MEMW);
	r_anal_esil_set_op(esil, "-=[]", smt_mem_subeq, 0, 2, OT_MATH | OT_MEMR | OT_MEMW);
	r_anal_esil_set_op(esil, "*=[]", smt_mem_muleq, 0, 2, OT_MATH | OT_MEMR | OT_MEMW);
	r_anal_esil_set_op(esil, "++=[]", smt_mem_inceq, 0, 1, OT_MATH | OT_MEMR | OT_MEMW);
	r_anal_esil_set_op(esil, "--=[]", smt_mem_deceq, 0, 1, OT_MATH | OT_MEMR | OT_MEMW);
	r_anal_esil_set_op(esil, "=[1]", smt_poke1, 0, 2, OT_MEMW);
	r_anal_esil_set_op(esil, "=[2]", smt_poke2, 0, 2, OT_MEMW);
	r_anal_esil_set_op(esil, "=[4]", smt_poke4, 0, 2, OT_MEMW);
	r_anal_esil_set_op(esil, "=[8]", smt_poke8, 0, 2, OT_MEMW);
	r_anal_esil_set_op(esil, "[1]", smt_peek1, 1, 1, OT_MEMR);
	r_anal_esil_set_op(esil, "[2]", smt_peek2, 1, 1, OT_MEMR);
	r_anal_esil_set_op(esil, "[4]", smt_peek4, 1, 1, OT_MEMR);
	r_anal_esil_set_op(esil, "[8]", smt_peek8, 1, 1, OT_MEMR);
	r_anal_esil_set_op(esil, "|=[1]", smt_mem_oreq1, 0, 2, OT_MATH | OT_MEMR | OT_MEMW);
	r_anal_esil_set_op(esil, "|=[2]", smt_mem_oreq2, 0, 2, OT_MATH | OT_MEMR | OT_MEMW);
	r_anal_esil_set_op(esil, "|=[4]", smt_mem_oreq4, 0, 2, OT_MATH | OT_MEMR | OT_MEMW);
	r_anal_esil_set_op(esil, "|=[8]", smt_mem_oreq8, 0, 2, OT_MATH | OT_MEMR | OT_MEMW);
	r_anal_esil_set_op(esil, "^=[1]", smt_mem_xoreq1, 0, 2, OT_MATH | OT_MEMR | OT_MEMW);
	r_anal_esil_set_op(esil, "^=[2]", smt_mem_xoreq2, 0, 2, OT_MATH | OT_MEMR | OT_MEMW);
	r_anal_esil_set_op(esil, "^=[4]", smt_mem_xoreq4, 0, 2, OT_MATH | OT_MEMR | OT_MEMW);
	r_anal_esil_set_op(esil, "^=[8]", smt_mem_xoreq8, 0, 2, OT_MATH | OT_MEMR | OT_MEMW);
	r_anal_esil_set_op(esil, "&=[1]", smt_mem_andeq1, 0, 2, OT_MATH | OT_MEMR | OT_MEMW);
	r_anal_esil_set_op(esil, "&=[2]", smt_mem_andeq2, 0, 2, OT_MATH | OT_MEMR | OT_MEMW);
	r_anal_esil_set_op(esil, "&=[4]", smt_mem_andeq4, 0, 2, OT_MATH | OT_MEMR | OT_MEMW);
	r_anal_esil_set_op(esil, "&=[8]", smt_mem_andeq8, 0, 2, OT_MATH | OT_MEMR | OT_MEMW);
	r_anal_esil_set_op(esil, "+=[1]", smt_mem_addeq1, 0, 2, OT_MATH | OT_MEMR | OT_MEMW);
	r_anal_esil_set_op(esil, "+=[2]", smt_mem_addeq2, 0, 2, OT_MATH | OT_MEMR | OT_MEMW);
	r_anal_esil_set_op(esil, "+=[4]", smt_mem_addeq4, 0, 2, OT_MATH | OT_MEMR | OT_MEMW);
	r_anal_esil_set_op(esil, "+=[8]", smt_mem_addeq8, 0, 2, OT_MATH | OT_MEMR | OT_MEMW);
	r_anal_esil_set_op(esil, "-=[1]", smt_mem_subeq1, 0, 2, OT_MATH | OT_MEMR | OT_MEMW);
	r_anal_esil_set_op(esil, "-=[2]", smt_mem_subeq2, 0, 2, OT_MATH | OT_MEMR | OT_MEMW);
	r_anal_esil_set_op(esil, "-=[4]", smt_mem_subeq4, 0, 2, OT_MATH | OT_MEMR | OT_MEMW);
	r_anal_esil_set_op(esil, "-=[8]", smt_mem_subeq8, 0, 2, OT_MATH | OT_MEMR | OT_MEMW);
	r_anal_esil_set_op(esil, "*=[1]", smt_mem_muleq1, 0, 2, OT_MATH | OT_MEMR | OT_MEMW);
	r_anal_esil_set_op(esil, "*=[2]", smt_mem_muleq2, 0, 2, OT_MATH | OT_MEMR | OT_MEMW);
	r_anal_esil_set_op(esil, "*=[4]", smt_mem_muleq4, 0, 2, OT_MATH | OT_MEMR | OT_MEMW);
	r_anal_esil_set_op(esil, "*=[8]", smt_mem_muleq8, 0, 2, OT_MATH | OT_MEMR | OT_MEMW);
	r_anal_esil_set_op(esil, "++=[1]", smt_mem_inceq1, 0, 1, OT_MATH | OT_MEMR | OT_MEMW);
	r_anal_esil_set_op(esil, "++=[2]", smt_mem_inceq2, 0, 1, OT_MATH | OT_MEMR | OT_MEMW);
	r_anal_esil_set_op(esil, "++=[4]", smt_mem_inceq4, 0, 1, OT_MATH | OT_MEMR | OT_MEMW);
	r_anal_esil_set_op(esil, "++=[8]", smt_mem_inceq8, 0, 1, OT_MATH | OT_MEMR | OT_MEMW);
	r_anal_esil_set_op(esil, "--=[1]", smt_mem_deceq1, 0, 1, OT_MATH | OT_MEMR | OT_MEMW);
	r_anal_esil_set_op(esil, "--=[2]", smt_mem_deceq2, 0, 1, OT_MATH | OT_MEMR | OT_MEMW);
	r_anal_esil_set_op(esil, "--=[4]", smt_mem_deceq4, 0, 1, OT_MATH | OT_MEMR | OT_MEMW);
	r_anal_esil_set_op(esil, "--=[8]", smt_mem_deceq8, 0, 1, OT_MATH | OT_MEMR | OT_MEMW);
	r_anal_esil_set_op(esil, "?{", smt_if, 0, 1, OT_CTR);
	r_anal_esil_set_op(esil, "}", smt_if_end, 0, 0, OT_CTR);

	return true;
}
