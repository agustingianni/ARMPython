from emulator.symbolic.base_expr import *
from emulator.symbolic.bitvector_expr import *
from emulator.symbolic.boolean_expr import *
from emulator.symbolic.misc_expr import *
from emulator.symbolic.memory import *
from emulator.symbolic.expression_z3 import *
import z3; wrap_module(z3)

def test():
    bv1=BvConstExpr.construct(0xcafecafe, 32)
    bv2=BvVarExpr.construct(32, "bv2")
    anded=(((bv1 & bv2) | 0x12345678) + 0xbababebe)
    anded2=(0xbababebe + (0x12345678 | (bv2 & bv1)))
    
    print hash(bv1)
    print hash(bv2)
    print hash(anded)
    print hash(anded2)
    d={}
    d[bv1]="bv1"
    d[bv2]="bv2"
    d[anded]="anded"
    print repr(d)
    d[anded2]="anded2"
    print repr(d)
    
    print bv2 == bv1
    print bv2 == bv2
    print bv2 + bv2
    print bv2 & bv2
    print bv2 ^ bv2
    
    print "%x" % bv1.extract(15,0)
    print bv2.extract(15,0)
    print "%x" % bv1.concat(BvConstExpr.construct(0xde, 8))
    print bv1.concat(bv2)
    print bv2.extract(31,0)
    
    c1=BvVarExpr.construct(8, "c1")
    c2=BvVarExpr.construct(8, "c2")
    c3=BvVarExpr.construct(8, "c3")
    c4=BvVarExpr.construct(8, "c4")
    w1=BvVarExpr.construct(16, "w1")
    d1=BvVarExpr.construct(32, "d1")
    
    d2=c1.concat(c2.concat(c3.concat(c4)))
    print d2
    d2=c1.concat(c2).concat(c3).concat(c4)
    print d2
    d2=c1.concat(c2).concat(c3.concat(c4))
    print d2
    print d2 >> 16
    print d2 << 24
    
    print "================================"
    
    for offset in (0, 8, 16, 24):
        for size in (8, 16, 24):
            if size + offset > 32:
                continue
            print "***********************"
            print "end=%d, start=%d" % (size+offset-1, offset) 
            out=d2.extract(size+offset-1,offset)
            if isinstance(out, BvExtractExpr):
                print d2
                print out
                     
    print "================**================"
    print bv2 + (-bv2)
    print d2 % 0x10000

    print "%x" % bv1.signExtend(64)
    print bv2.signExtend(64)

    print "%x" % bv1.zeroExtend(64)
    print bv2.zeroExtend(64)
    
    print "================================"
    print bv1 + ((bv2 + bv1) + bv2)
    print (bv1 + bv2) + bv1

    print "================================"
    print bv2 * bv2 * 3 * 5
    print 5 * bv2 * 3 * bv2
    print 3 * bv2 * 5 * bv2 * 7

    print "================================"
    print ((bv2 + bv2) + bv2) + bv2
    print (bv2 + bv2) + (bv2 + bv2)
    print bv2 + ((bv2 + bv2) + bv2)
    print bv2 + (bv2 + (bv2 + bv2))

    print "================================"
    print bv2 & 0xcafe
    
    print "CACHE STATS"
    for cls in (BvConstExpr, BvVarExpr, BvConcatExpr, BvExtractExpr, BvNotExpr, BvNegExpr, \
                BvAndExpr, BvOrExpr, BvXorExpr, BvAddExpr, BvSubExpr, BvMulExpr, \
                BvUDivExpr, BvURemExpr, BvShlExpr, BvShrExpr, \
                BvUgtExpr, BvUgeExpr, BvUltExpr, BvUleExpr, \
                BvIteExpr):
        print "%s: hits=%d, misses=%d" % (cls.__name__, cls.construct.hits, cls.construct.misses)
    
    for cls in (BoolNotExpr, BoolAndExpr, BoolOrExpr, BoolXorExpr, BoolImplExpr, \
                BoolVarExpr, EqExpr, DistinctExpr, BoolIteExpr):
        print "%s: hits=%d, misses=%d" % (cls.__name__, cls.construct.hits, cls.construct.misses)
    
    print
    print "BOOLEAN CACHE"
    for k,v in BoolExprCache.cache.iteritems():
        print "%s ==> %s (used=%d)" % (k,v,BoolExprCache.uses[hash(v)])

    print
    print "BITVECTOR CACHE"
    for k,v in BvExprCache.cache.iteritems():
        print "%s ==> %s (used=%d)" % (k,v,BvExprCache.uses[hash(v)])
    
    print "================================"
    b1 = BoolVarExpr()
    a=(((bv2 + bv2) + bv2) + bv2 == 0) == b1
    a=d2.extract(12, 0) == 0xcafecafe
    print a
    (decl, asser, expr) = a.export_smtlib2(0)
    print decl
    print asser
    print expr
    
    print "================================"
    mem = AbstractMemoryMap()
    mem.set_dword(0xcafecafe, 0xdeadbeef)
    mem.set_dword(bv2, 0xbabadada)
    
    print "%x" % mem.get_dword(0xcafecafe)
    a = mem.get_dword(bv2 + 1) == 0xcababada
    print a
    
    #quantitier free, arrays, unintepreted funtions and bitvectors    
    s=z3.SolverFor("QF_AUFBV")
    s.add(a) #add constrain
    print s.check()
    m = s.model()
    
    #check the transparent flow between BvExprs and Z3 stuff
    z3_expr = m.eval(mem.get_dword(bv2 + 1))
    print "%x" % z3_expr.as_long()
    
    #and the other way around
    print z3.simplify(mem.get_dword(bv2 * 0xdafe)).toExpr()

    #smtlib2 version:
    #ExportParameters().clear()
    #ExportParameters().set_mindepth(0)
    #mem.export()
    #e=a.export()
    #print "\n".join(ExportParameters().get_decls())
    #print "(assert " + ")\n(assert ".join(ExportParameters().get_asserts()) + ")"
    #print "(assert %s)" % e


if __name__=="__main__":
    test()
