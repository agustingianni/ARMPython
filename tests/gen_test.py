import sys
from arm import ARMDisasembler
from arm import UnpredictableInstructionException
from arm import InstructionNotImplementedException
from subprocess import check_output

assembler = "arm-linux-androideabi-as"
disassembler = "arm-linux-androideabi-objdump"

def assemble():
	output = check_output([assembler, "-o", "test.o", "test.s"])
	return output

def disassemble(opcode):
	output = check_output([disassembler, "-d", "test.o"])
	res = []
	for line in output.split("\n"):
		t = line.split()
		if not len(t) or not (opcode in t):
			continue
		
		op = int(t[1], 16)
		
		# dis = t[2:]
		if not (';' in t[2:]):
			dis = t[2:]
		else:
			# Drop the comment in a really ghetto way
			idx = t[2:].index(";")
			dis = t[2:2 + idx]
		
		res.append((op, " ".join(dis)))

	return res

def gen_reg_wb_regs(fd, opcode):
	# Generate test cases for 
	# op Rx, <register_list>
	wbs = ""
	for wb in xrange(0, 2):
		for r1 in xrange(0, 15):
			for regs in xrange(1, 17):
				if wb:
					wbs = "!"
					
				fd.write("%s r%d%s, %s\n" % (opcode, r1, wbs, get_regs((1 << regs) - 1)))

shifts = ["lsl", "lsr", "asr", "ror"]

def gen_reg_reg_reg_shift_reg(fd, opcode):
	for r1 in xrange(0, 16):
		for r2 in xrange(0, 16):
			for r3 in xrange(0, 16):
				for s1 in shifts:
					for rs in xrange(0, 16):
						fd.write("%s r%d, r%d, r%d, %s r%d\n" % (opcode, r1, r2, r3, s1, rs))

def gen_reg_reg_reg(fd, opcode):
	# Generate test cases for 
	# op Rx, Ry, Rz
	for r1 in xrange(0, 16):
		for r2 in xrange(0, 16):
			for r3 in xrange(0, 16):
				fd.write("%s r%d, r%d, r%d\n" % (opcode, r1, r2, r3))

def gen_reg(fd, opcode, low_limit=0, hi_limit=16):
	# Generate test cases for 
	# op Rx
	for r1 in xrange(low_limit, hi_limit):
		fd.write("%s r%d\n" % (opcode, r1))

def gen_reg_imm(fd, opcode):
	# Generate test cases for 
	# op Rx, #imm
	for r1 in xrange(0, 16):
		fd.write("%s r%d, #%d\n" % (opcode, r1, 4))

def gen_reg_reg(fd, opcode, max_r1=16, max_r2=16):
	# Generate test cases for 
	# op Rx, Ry
	for r1 in xrange(0, max_r1):
		for r2 in xrange(0, max_r2):
			fd.write("%s r%d, r%d\n" % (opcode, r1, r2))

def gen_reg_reg_imm(fd, opcode):
	# Generate test cases for 
	# op Rx, Ry, #imm
	for r1 in xrange(0, 16):
		for r2 in xrange(0, 16):
			fd.write("%s r%d, r%d, #%d\n" % (opcode, r1, r2, 4))

def gen_reg_reg_reg_shift_imm(fd, opcode):
	# Generate test cases for
	# op Rx, Ry, Rz shift_type imm
	for r1 in xrange(0, 16):
		for r2 in xrange(0, 16):
			for r3 in xrange(0, 16):
				for s1 in shifts:
					fd.write("%s r%d, r%d, r%d, %s #%d\n" % (opcode, r1, r2, r3, s1, 8))

def gen_reg_reg_shift_reg(fd, opcode):
	# Generate test cases for
	# op Rx, Ry, shift_type Rz
	for r1 in xrange(0, 16):
		for r2 in xrange(0, 16):
			for r3 in xrange(0, 16):
				for s1 in shifts:
					fd.write("%s r%d, r%d, %s r%d\n" % (opcode, r1, r2, s1, r3))

def gen_reg_reg_shift_imm(fd, opcode):
	# Generate test cases for
	# op Rx, Ry, shift_type #imm
	for r1 in xrange(0, 16):
		for r2 in xrange(0, 16):
			for s1 in shifts:
				fd.write("%s r%d, r%d, %s #%d\n" % (opcode, r1, r2, s1, 4))

def gen_reg_label(fd, opcode):
	fd.write("label_1: nop\n")
	for r1 in xrange(0, 16):
		fd.write("%s r%d, label_1\n" % (opcode, r1))

def gen_label(fd, opcode):
	fd.write("label_1: nop\n")
	fd.write("%s label_1\n" % (opcode))

def validate(arm_dis, res, show=False):
	for r in res:
		try:
			o = arm_dis.disassemble(r[0])
			if not o:
				print "  OPCode  : %.8x" % r[0] 
				print "  objdump :", map(lambda x: x.lower(), r[1].split())  
				raise Exception("Our disassembler returned null")
			
			if set(map(lambda x: x.lower(), r[1].split())) != set(map(lambda x: x.lower(), o.split())):
				t = o.split()
				if t[-2] == "lsl" and t[-1] == "#0":
					continue

				if "UNPREDICTABLE" in r[1]:
					# Should not appear
					print "Unpredictable"
					continue
							
				print "Difference!:"
				print "  OPCode  : %.8x" % r[0] 
				print "  objdump :", map(lambda x: x.lower(), r[1].split())  
				print "  ours    :", map(lambda x: x.lower(), o.split())
				
			elif show:
				print "Match!:"
				print "  OPCode  : %.8x" % r[0] 
				print "  objdump :", map(lambda x: x.lower(), r[1].split())  
				print "  ours    :", map(lambda x: x.lower(), o.split())
				
	
		except UnpredictableInstructionException:
			# print "Unpredictable"
			continue
		
		except InstructionNotImplementedException, e:
			print "Not Implemented"
			print "  OPCode  : %.8x" % r[0] 
			print "  objdump :", map(lambda x: x.lower(), r[1].split())
			print e
			
			continue

def test_adc(arm_dis):
	# This only tests eEncodingA1
	op = "adc"
	f = open("test.s", "w")
	
	gen_reg_reg_imm       (f, op)
	gen_reg_reg_reg       (f, op)
	gen_reg_reg_reg_shift_reg (f, op)
	gen_reg_reg_shift_imm (f, op)
	
	f.close()
	assemble()
	
	res = disassemble(op)
	validate(arm_dis, res)

def test_and(arm_dis):
	# This only tests eEncodingA1
	op = "and"
	f = open("test.s", "w")
	
	gen_reg_reg_imm       (f, op)
	gen_reg_reg_reg       (f, op)
	gen_reg_reg_reg_shift_reg (f, op)
	gen_reg_reg_shift_imm (f, op)
	
	f.close()
	assemble()
	
	res = disassemble(op)
	validate(arm_dis, res)

def test_add(arm_dis):
	# This only tests eEncodingA1
	op = "add"
	f = open("test.s", "w")
	
	gen_reg_reg_imm       (f, op)
	gen_reg_reg_reg       (f, op)
	gen_reg_reg_reg_shift_reg (f, op)
	gen_reg_reg_shift_imm (f, op)
	
	f.close()
	assemble()
	
	res = disassemble(op)
	validate(arm_dis, res)

def test_adr(arm_dis):
	# FIXME: FAILS
	# This only tests eEncodingA1
	op = "adr"
	f = open("test.s", "w")
	
	gen_reg_label(f, op)
	
	f.close()
	assemble()
	
	# op is changed from adr to sub	
	res = disassemble("sub")
	validate(arm_dis, res, show=True)

def test_asr(arm_dis):
	# This only tests eEncodingA1
	op = "asr"
	f = open("test.s", "w")
	
	gen_reg_reg_imm(f, op)
	gen_reg_reg_reg(f, op)
	
	f.close()
	assemble()
	
	res = disassemble(op)
	validate(arm_dis, res)

def test_b(arm_dis):
	# FIXME: FAILS
	# This only tests eEncodingA1
	op = "b"
	f = open("test.s", "w")
	
	gen_label(f, op)
	
	f.close()
	assemble()
	
	res = disassemble(op)
	validate(arm_dis, res)

def test_bl(arm_dis):
	# FIXME: FAILS
	# This only tests eEncodingA1
	op = "bl"
	f = open("test.s", "w")
	
	gen_label(f, op)
	
	f.close()
	assemble()
	
	res = disassemble(op)
	validate(arm_dis, res)

def test_blx(arm_dis):
	# FIXME: FAILS
	# This only tests eEncodingA1
	op = "blx"
	f = open("test.s", "w")
	
	gen_reg(f, op, 0, 15)
	
	f.close()
	assemble()
	
	res = disassemble(op)
	validate(arm_dis, res, True)


def test_bic(arm_dis):
	# This only tests eEncodingA1
	op = "bic"
	f = open("test.s", "w")
	
	gen_reg_reg_imm       (f, op)
	gen_reg_reg_reg       (f, op)
	gen_reg_reg_reg_shift_reg (f, op)
	
	f.close()
	assemble()
	
	res = disassemble(op)
	validate(arm_dis, res)

def test_cmn(arm_dis):
	# This only tests eEncodingA1
	op = "cmn"
	f = open("test.s", "w")
	
	gen_reg_imm           (f, op)
	gen_reg_reg           (f, op)
	gen_reg_reg_shift_reg (f, op)
	
	f.close()
	assemble()
	
	res = disassemble(op)
	validate(arm_dis, res)

def test_cmp(arm_dis):
	# This only tests eEncodingA1
	op = "cmp"
	f = open("test.s", "w")
	
	gen_reg_imm           (f, op)
	gen_reg_reg           (f, op)
	gen_reg_reg_shift_reg (f, op)
	
	f.close()
	assemble()
	
	res = disassemble(op)
	validate(arm_dis, res)

def test_eor(arm_dis):
	# This only tests eEncodingA1
	op = "eor"
	f = open("test.s", "w")
	
	gen_reg_reg_imm           (f, op)
	gen_reg_reg_reg           (f, op)
	gen_reg_reg_reg_shift_reg (f, op)
	
	f.close()
	assemble()
	
	res = disassemble(op)
	validate(arm_dis, res)

def get_regs(reglist):
	t = []
	for i in xrange(0, 16):
		if ((1 << i) & reglist):
			t.append("r%d" % i)
	
	return "{" + ",".join(t) + "}" 
	
def test_ldm(arm_dis):
	# This only tests eEncodingA1
	op = "ldm"
	f = open("test.s", "w")
	
	gen_reg_wb_regs(f, op)
	
	f.close()
	assemble()
	
	res = disassemble(op)
	validate(arm_dis, res, show=False)
	
def test_ldmda(arm_dis):
	# This only tests eEncodingA1
	op = "ldmda"
	f = open("test.s", "w")
	
	gen_reg_wb_regs(f, op)
	
	f.close()
	assemble()
	
	res = disassemble(op)
	validate(arm_dis, res, show=False)

def test_ldmdb(arm_dis):
	# This only tests eEncodingA1
	op = "ldmdb"
	f = open("test.s", "w")
	
	gen_reg_wb_regs(f, op)
	
	f.close()
	assemble()
	
	res = disassemble(op)
	validate(arm_dis, res, show=False)
	
def test_ldmia(arm_dis):
	# This only tests eEncodingA1
	op = "ldmia"
	f = open("test.s", "w")
	
	gen_reg_wb_regs(f, op)
	
	f.close()
	assemble()
	
	res = disassemble(op)
	validate(arm_dis, res, show=False)

def test_ldmib(arm_dis):
	# This only tests eEncodingA1
	op = "ldmib"
	f = open("test.s", "w")
	
	gen_reg_wb_regs(f, op)
	
	f.close()
	assemble()
	
	res = disassemble(op)
	validate(arm_dis, res, show=False)

def test_lsl(arm_dis):
	# This only tests eEncodingA1
	op = "lsl"
	f = open("test.s", "w")
	
	gen_reg_reg_imm(f, op)
	gen_reg_reg(f, op)
	
	f.close()
	assemble()
	
	res = disassemble(op)
	validate(arm_dis, res, show=False)

def test_lsr(arm_dis):
	# This only tests eEncodingA1
	op = "lsr"
	f = open("test.s", "w")
	
	gen_reg_reg_imm(f, op)
	gen_reg_reg(f, op)
	
	f.close()
	assemble()
	
	res = disassemble(op)
	validate(arm_dis, res, show=False)



def gen_reg_imm16(fd, opcode):
	for r1 in xrange(0, 15):
		for i in xrange(0, 16):
			fd.write("%s r%d, #%d\n" % (opcode, r1, (1 << i)))
	
def gen_mov_reg_imm(fd, opcode):
	# Generate test cases for 
	# op Rx, #imm
	for r1 in xrange(0, 15):
		fd.write("%s r%d, #%d\n" % (opcode, r1, 4))

def test_mov_imm(arm_dis):
	# This only tests eEncodingA1
	op = "movw"
	f = open("test.s", "w")
	
	gen_mov_reg_imm(f, op)

	f.close()
	assemble()
	
	res = disassemble(op)
	validate(arm_dis, res, show=False)

def test_mov(arm_dis):
	# This only tests eEncodingA1
	op = "mov"
	f = open("test.s", "w")
	
	gen_reg_reg(f, op)
	# gen_mov_reg_imm(f, op)

	f.close()
	assemble()
	
	res = disassemble(op)
	validate(arm_dis, res, show=True)

def test_movt(arm_dis):
	# This only tests eEncodingA1
	op = "movt"
	f = open("test.s", "w")
	
	gen_reg_imm16(f, op)

	f.close()
	assemble()
	
	res = disassemble(op)
	validate(arm_dis, res, show=True)

def test_mvn(arm_dis):
	# This only tests eEncodingA1
	op = "mvn"
	f = open("test.s", "w")
	
	gen_reg_imm(f, op)
	gen_reg_reg(f, op)
	gen_reg_reg_shift_imm(f, op)
	gen_reg_reg_shift_reg(f, op)

	f.close()
	assemble()
	
	res = disassemble(op)
	validate(arm_dis, res, show=False)

def test_orr(arm_dis):
	# This only tests eEncodingA1
	op = "orr"
	f = open("test.s", "w")
	
	gen_reg_reg_imm(f, op)
	gen_reg_reg_shift_imm(f, op)
	gen_reg_reg_shift_reg(f, op)

	f.close()
	assemble()	
	
	res = disassemble(op)
	validate(arm_dis, res, show=False)

def gen_pop(fd, opcode):
	for regs in xrange(1, 17):			
		fd.write("%s %s\n" % (opcode, get_regs((1 << regs) - 1)))

def test_pop(arm_dis):
	# This only tests eEncodingA1
	op = "pop"
	f = open("test.s", "w")
	
	gen_pop(f, op)

	f.close()
	assemble()	
	
	res = disassemble(op)
	validate(arm_dis, res, show=False)

def gen_push(fd, opcode):
	for regs in xrange(1, 17):			
		fd.write("%s %s\n" % (opcode, get_regs((1 << regs) - 1)))

def test_push(arm_dis):
	# This only tests eEncodingA1
	op = "push"
	f = open("test.s", "w")
	
	gen_push(f, op)

	f.close()
	assemble()	
	
	res = disassemble(op)
	validate(arm_dis, res, show=False)

def test_ror(arm_dis):
	# This only tests eEncodingA1
	op = "ror"
	f = open("test.s", "w")
	
	gen_reg_reg_imm(f, op)
	gen_reg_reg_reg(f, op)

	f.close()
	assemble()	
	
	res = disassemble(op)
	validate(arm_dis, res, show=False)

def test_rrx(arm_dis):
	# This only tests eEncodingA1
	op = "rrx"
	f = open("test.s", "w")
	
	gen_reg_reg(f, op)

	f.close()
	assemble()	
	
	res = disassemble(op)
	validate(arm_dis, res, show=False)

def test_rsb(arm_dis):
	# This only tests eEncodingA1
	op = "rsb"
	f = open("test.s", "w")
	
	gen_reg_reg_imm(f, op)
	gen_reg_reg_reg_shift_imm(f, op)
	gen_reg_reg_reg_shift_reg(f, op)

	f.close()
	assemble()	
	
	res = disassemble(op)
	validate(arm_dis, res, show=False)

def test_rsc(arm_dis):
	# This only tests eEncodingA1
	op = "rsc"
	f = open("test.s", "w")
	
	gen_reg_reg_imm(f, op)
	gen_reg_reg_reg_shift_imm(f, op)
	gen_reg_reg_reg_shift_reg(f, op)

	f.close()
	assemble()	
	
	res = disassemble(op)
	validate(arm_dis, res, show=False)

def test_sbc(arm_dis):
	# This only tests eEncodingA1
	op = "sbc"
	f = open("test.s", "w")
	
	gen_reg_reg_imm(f, op)
	gen_reg_reg_reg_shift_imm(f, op)
	gen_reg_reg_reg_shift_reg(f, op)

	f.close()
	assemble()	
	
	res = disassemble(op)
	validate(arm_dis, res, show=False)

def test_sub(arm_dis):
	# This only tests eEncodingA1
	op = "sub"
	f = open("test.s", "w")
	
	gen_reg_reg_imm(f, op)
	gen_reg_reg_reg_shift_imm(f, op)
	gen_reg_reg_reg_shift_reg(f, op)

	f.close()
	assemble()	
	
	res = disassemble(op)
	validate(arm_dis, res, show=True)

def gen_imm(fd, opcode):
	for i in xrange(0, 50):			
		fd.write("%s #%d\n" % (opcode, i))

def test_svc(arm_dis):
	# This only tests eEncodingA1
	op = "svc"
	f = open("test.s", "w")
	
	gen_imm(f, op)

	f.close()
	assemble()	
	
	res = disassemble(op)
	validate(arm_dis, res, show=False)

def test_teq(arm_dis):
	# This only tests eEncodingA1
	op = "teq"
	f = open("test.s", "w")
	
	gen_reg_imm(f, op)
	gen_reg_reg_shift_imm(f, op)
	gen_reg_reg_shift_reg(f, op)

	f.close()
	assemble()	
	
	res = disassemble(op)
	validate(arm_dis, res, show=False)

def test_tst(arm_dis):
	# This only tests eEncodingA1
	op = "tst"
	f = open("test.s", "w")
	
	gen_reg_imm(f, op)
	gen_reg_reg_shift_imm(f, op)
	gen_reg_reg_shift_reg(f, op)

	f.close()
	assemble()	
	
	res = disassemble(op)
	validate(arm_dis, res, show=False)

def test_bx_reg(arm_dis):
	# This only tests eEncodingA1
	op = "bx"
	f = open("test.s", "w")
	
	gen_reg(f, op)

	f.close()
	assemble()	
	
	res = disassemble(op)
	validate(arm_dis, res, show=True)

def test_clz(arm_dis):
	# This only tests eEncodingA1
	op = "clz"
	f = open("test.s", "w")
	
	gen_reg_reg(f, op, max_r1=15, max_r2=15)

	f.close()
	assemble()	
	
	res = disassemble(op)
	validate(arm_dis, res, show=True)

def test_eret(arm_dis):
	# This only tests eEncodingA1
	op = "eret"
	f = open("test.s", "w")
	
	f.write("eret\n");

	f.close()
	assemble()	
	
	res = disassemble(op)
	validate(arm_dis, res, show=True)

def test_bkpt(arm_dis):
	# This only tests eEncodingA1
	op = "bkpt"
	f = open("test.s", "w")
	
	for i in xrange(0, 16):
		f.write("bkpt #%d\n" % (1 << i));

	f.close()
	assemble()	
	
	res = disassemble(op)
	validate(arm_dis, res, show=True)

def test_dbg(arm_dis):
	# This only tests eEncodingA1
	op = "dbg"
	f = open("test.s", "w")
	
	for i in xrange(0, 4):
		f.write("dbg #%d\n" % (1 << i));

	f.close()
	assemble()	
	
	res = disassemble(op)
	validate(arm_dis, res, show=True)


def test_bxj(arm_dis):
	# This only tests eEncodingA1
	op = "bxj"
	f = open("test.s", "w")
	
	gen_reg(f, op, 0, 15)

	f.close()
	assemble()	
	
	res = disassemble(op)
	validate(arm_dis, res, show=True)

def test_blx_reg(arm_dis):
	# This only tests eEncodingA1
	op = "blx"
	f = open("test.s", "w")
	
	gen_reg(f, op)

	f.close()
	assemble()	
	
	res = disassemble(op)
	validate(arm_dis, res, show=True)

def gen_reg_reg_imm8(fd, opcode):
	for r1 in xrange(0, 16):
		for r2 in xrange(0, 16):
			for i in xrange(0, 8):
				fd.write("%s r%d, r%d, #%d\n" % (opcode, r1, r2, 1 << i))
	

def gen_reg_mem_reg_imm8(fd, opcode):
	for r1 in xrange(0, 16):
		for r2 in xrange(0, 16):
			for i in xrange(0, 8):
				fd.write("%s r%d, [r%d, #%d]\n" % (opcode, r1, r2, 1 << i))

def test_ldrex(arm_dis):
	op = "ldrex"
	f = open("test.s", "w")
	
	gen_reg_mem_reg_imm8(f, op)

	f.close()
	assemble()	
	
	res = disassemble(op)
	validate(arm_dis, res, show=True)	
	
def test_str_imm_arm(arm_dis):
	op = "str"
	f = open("test.s", "w")
	
	for Rt in xrange(0, 16):
		if Rt == 15:
			continue
		
		for Rn in xrange(0, 16):
			if Rn == 15 or Rt == Rn:
				continue
			
			for i in xrange(0, 12):
				f.write("STR r%d, [r%d, #%d]\n" % (Rt, Rn, 1 << i))
				f.write("STR r%d, [r%d, #%d]!\n" % (Rt, Rn, 1 << i))
				f.write("STR r%d, [r%d], #%d\n" % (Rt, Rn, 1 << i))

				f.write("STR r%d, [r%d, #-%d]\n" % (Rt, Rn, 1 << i))
				f.write("STR r%d, [r%d, #-%d]!\n" % (Rt, Rn, 1 << i))
				f.write("STR r%d, [r%d], #-%d\n" % (Rt, Rn, 1 << i))
			
			
	f.close()
	assemble()	
	
	res = disassemble(op)
	validate(arm_dis, res, show=True)	
	
def test_strt(arm_dis):
	op = "strt"
	f = open("test.s", "w")

	for Rt in xrange(0, 16):
		if Rt == 15:
			continue
		
		for Rn in xrange(0, 16):
			if Rn == 15 or Rt == Rn:
				continue
			for i in xrange(0, 12):
				f.write("%s r%d, [r%d], #%d\n" % (op, Rt, Rn, 1 << i))
				f.write("%s r%d, [r%d], #-%d\n" % (op, Rt, Rn, 1 << i))

	for Rt in xrange(0, 16):
		if Rt == 15:
			continue
		
		for Rn in xrange(0, 16):
			if Rn == 15 or Rt == Rn:
				continue

			for Rm in xrange(0, 16):
				if Rm == 15:
					continue

				for s1 in shifts:
					f.write("%s r%d, [r%d], r%d, %s #%d\n" % (op, Rt, Rn, Rm, s1, 8))
				
	f.close()
	assemble()	
	
	res = disassemble(op)
	validate(arm_dis, res, show=True)	

def test_ldrt(arm_dis):
	op = "ldrt"
	f = open("test.s", "w")

	for Rt in xrange(0, 16):
		if Rt == 15:
			continue
		
		for Rn in xrange(0, 16):
			if Rn == 15 or Rt == Rn:
				continue
			
			for i in xrange(0, 12):
				# f.write("%s r%d, [r%d, #%d]\n" % (op, Rt, Rn, 1 << i))
				f.write("%s r%d, [r%d], #%d\n" % (op, Rt, Rn, 1 << i))
				f.write("%s r%d, [r%d], #-%d\n" % (op, Rt, Rn, 1 << i))

	for Rt in xrange(0, 16):
		if Rt == 15:
			continue
		
		for Rn in xrange(0, 16):
			if Rn == 15 or Rt == Rn:
				continue

			for Rm in xrange(0, 16):
				if Rm == 15:
					continue

				for s1 in shifts:
					f.write("%s r%d, [r%d], r%d, %s #%d\n" % (op, Rt, Rn, Rm, s1, 8))
					f.write("%s r%d, [r%d], -r%d, %s #%d\n" % (op, Rt, Rn, Rm, s1, 8))
				
	f.close()
	assemble()	
	
	res = disassemble(op)
	validate(arm_dis, res, show=True)	

def test_ldr_literal(arm_dis):
	op = "ldr"
	f = open("test.s", "w")

	for Rt in xrange(0, 16):
		for i in xrange(0, 12):
			f.write("LDR r%d, [r%d, #%d]\n" % (Rt, 15, 1 << i))
			f.write("LDR r%d, [r%d, #-%d]\n" % (Rt, 15, 1 << i))
		
	f.close()
	assemble()	
	
	res = disassemble(op)
	validate(arm_dis, res, show=True)	

def ldr_register_arm(arm_dis):
	op = "ldr"
	f = open("test.s", "w")

	for Rt in xrange(0, 16):
		# if Rt == 15:
		# 	continue
		
		for Rn in xrange(0, 16):
			if Rn == 15 or Rt == Rn:
				continue

			for Rm in xrange(0, 16):
				if Rm == 15:
					continue

				for s1 in shifts:
					f.write("%s r%d, [r%d, r%d, %s #%d]\n" % (op, Rt, Rn, Rm, s1, 8))
					f.write("%s r%d, [r%d, -r%d, %s #%d]\n" % (op, Rt, Rn, Rm, s1, 8))
					f.write("%s r%d, [r%d, r%d, %s #%d]!\n" % (op, Rt, Rn, Rm, s1, 8))
					f.write("%s r%d, [r%d, -r%d, %s #%d]!\n" % (op, Rt, Rn, Rm, s1, 8))
					f.write("%s r%d, [r%d], r%d, %s #%d\n" % (op, Rt, Rn, Rm, s1, 8))
					f.write("%s r%d, [r%d], -r%d, %s #%d\n" % (op, Rt, Rn, Rm, s1, 8))
				
	f.close()
	assemble()	
	
	res = disassemble(op)
	validate(arm_dis, res, show=True)	

def test_str_reg(arm_dis):
	op = "str"
	f = open("test.s", "w")

	for Rt in xrange(0, 16):
		if Rt == 15:
			continue
		
		for Rn in xrange(0, 16):
			if Rn == 15 or Rt == Rn:
				continue

			for Rm in xrange(0, 16):
				if Rm == 15:
					continue

				for s1 in shifts:
					f.write("%s r%d, [r%d, r%d, %s #%d]\n" % (op, Rt, Rn, Rm, s1, 8))
					f.write("%s r%d, [r%d, r%d, %s #%d]!\n" % (op, Rt, Rn, Rm, s1, 8))
					f.write("%s r%d, [r%d], r%d, %s #%d\n" % (op, Rt, Rn, Rm, s1, 8))
				
	f.close()
	assemble()	
	
	res = disassemble(op)
	validate(arm_dis, res, show=True)	

def test_srs_arm(arm_dis):
	op = "srsda"
	f = open("test.s", "w")

	f.write("%s SP%s, #%d\n" % (op, "!", 8))
	f.write("%s SP%s, #%d\n" % (op, "", 8))

	f.close()
	assemble()	
	
	res = disassemble(op)
	validate(arm_dis, res, show=True)	

def test_rfe(arm_dis):
	op = "rfeda"
	f = open("test.s", "w")

	for Rn in xrange(0, 15):
		f.write("%s r%s%s\n" % (op, Rn, "!"))
		f.write("%s r%s%s\n" % (op, Rn, ""))

	f.close()
	assemble()	
	
	res = disassemble(op)
	validate(arm_dis, res, show=True)	


	
arm_dis = ARMDisasembler()
# test_adc(arm_dis)
# test_and(arm_dis)
# test_add(arm_dis)
# test_adr(arm_dis)
# test_asr(arm_dis)
# test_b(arm_dis)
# test_bl(arm_dis)
# test_blx(arm_dis)
# test_bic(arm_dis)
# test_cmn(arm_dis)
# test_cmp(arm_dis)
# test_eor(arm_dis)
# test_ldm(arm_dis)
# test_ldmda(arm_dis)
# test_ldmdb(arm_dis)
# test_ldmia(arm_dis)
# test_ldmib(arm_dis)
# test_lsl(arm_dis)
# test_lsr(arm_dis)
# test_mov(arm_dis)
# test_movt(arm_dis)
# test_mvn(arm_dis)
# test_orr(arm_dis)
# test_pop(arm_dis)
# test_push(arm_dis)
# test_ror(arm_dis)
# test_rrx(arm_dis)
# test_rsb(arm_dis)
# test_rsc(arm_dis)
# test_sbc(arm_dis)
# test_sub(arm_dis)
# test_svc(arm_dis)
# test_teq(arm_dis)
# test_tst(arm_dis)
# test_bx_reg(arm_dis)
# test_clz(arm_dis)
# test_eret(arm_dis)
# test_bxj(arm_dis)
# test_blx_reg(arm_dis)
# test_bkpt(arm_dis)
# test_dbg(arm_dis)
# test_ldrex(arm_dis)
# test_str_imm_arm(arm_dis)
# test_str_reg(arm_dis)
# test_strt(arm_dis)
# test_ldr_literal(arm_dis)
# ldr_register_arm(arm_dis)
# test_ldrt(arm_dis)
#test_srs_arm(arm_dis)
test_rfe(arm_dis)
