from emulator.symbolic.base_expr import *
from emulator.symbolic.bitvector_expr import *
from emulator.symbolic.boolean_expr import *
from emulator.symbolic.misc_expr import *

def test():
    bv1=BvConstExpr(0xcafecafe, 32)
    bv2=BvVarExpr(32, "bv2")
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
    print "%x" % bv1.concat(BvConstExpr(0xde, 8))
    print bv1.concat(bv2)
    print bv2.extract(31,0)
    
    c1=BvVarExpr(8, "c1")
    c2=BvVarExpr(8, "c2")
    c3=BvVarExpr(8, "c3")
    c4=BvVarExpr(8, "c4")
    w1=BvVarExpr(16, "w1")
    d1=BvVarExpr(32, "d1")
    
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
                     
    print "================================"
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
    print (bv2 + bv2) + (bv2 + bv2)

if __name__=="__main__":
    test()
