'''
Created on Jul 29, 2013

@author: anon
'''
import zmq
import sys
import struct
from emulator.ARMEmulator import ARMEmulator, ExecutionContext
from disassembler.tests.tablecheck import arm_opcodes, get_masked_random
from emulator.memory import NullMemoryMap
from disassembler.constants.arm import ARMRegister, ARMFLag, ARMMode
from disassembler.arm import ARMDisassembler
from disassembler.arch import UnpredictableInstructionException, Register,\
    InstructionNotImplementedException, ProcessorFlag
from disassembler.utils.bits import get_bit

class ObserverClient(object):
    def __init__(self):
        """
        Initialize the context and socket of ZMQ
        """
        self.context = zmq.Context()
        self.socket = self.context.socket(zmq.REQ)

    def connect(self, host):
        """
        Connect to the remote endpoint.
        """
        #  Socket to talk to server
        print "Connecting to %s server..." % host
        self.socket.connect ("tcp://%s:4141" % host)
        
    def message(self, message):
        """
        Send a message to the endpoint.
        """
        self.socket.send (message)    
        message = self.socket.recv()
        
        return message

def StringToContext(values):
    """
    Values is a list of strings in the following format:
        
        '<reg>=<value>'
        
    """
    register_map = {}
    register_map[ARMRegister.R0.reg] = int(values[0].split("=")[1])
    register_map[ARMRegister.R1.reg] = int(values[1].split("=")[1])
    register_map[ARMRegister.R2.reg] = int(values[2].split("=")[1])
    register_map[ARMRegister.R3.reg] = int(values[3].split("=")[1])
    register_map[ARMRegister.R4.reg] = int(values[4].split("=")[1])
    register_map[ARMRegister.R5.reg] = int(values[5].split("=")[1])
    register_map[ARMRegister.R6.reg] = int(values[6].split("=")[1])
    register_map[ARMRegister.R7.reg] = int(values[7].split("=")[1])
    register_map[ARMRegister.R8.reg] = int(values[8].split("=")[1])
    register_map[ARMRegister.R9.reg] = int(values[9].split("=")[1])
    register_map[ARMRegister.R10.reg] = int(values[10].split("=")[1])
    register_map[ARMRegister.R11.reg] = int(values[11].split("=")[1])
    register_map[ARMRegister.R12.reg] = int(values[12].split("=")[1])
    register_map[ARMRegister.R13.reg] = int(values[13].split("=")[1])
    register_map[ARMRegister.R14.reg] = int(values[14].split("=")[1])
    register_map[ARMRegister.R15.reg] = int(values[15].split("=")[1])
    
    flags = int(values[16].split("=")[1])
        
    flags_map = {}
    flags_map[ARMFLag.N] = get_bit(flags, 31)
    flags_map[ARMFLag.Z] = get_bit(flags, 30)
    flags_map[ARMFLag.C] = get_bit(flags, 29)
    flags_map[ARMFLag.V] = get_bit(flags, 28)
    flags_map[ARMFLag.Q] = get_bit(flags, 27)
    
    return ExecutionContext(register_map, flags_map)

def CompareContexts(local, remote):
    """
    Compare execution contexts. 
    """
    ret = []
    for name in local.regs.keys():
        if local.regs[name] != remote.regs[name]:
            ret.append(("register", name, local.regs[name], remote.regs[name]))
            
    for name in local.flags.keys():
        if local.flags[name] != remote.flags[name]:
            ret.append(("flag", name, local.flags[name], remote.flags[name]))
            
    return ret

if __name__ == '__main__':
    client = ObserverClient()
    client.connect("localhost")
    
    null_map = NullMemoryMap()
    emulator = ARMEmulator(null_map)
    disassembler = ARMDisassembler()
    
    limit = 100
    
    for i in xrange(0, len(arm_opcodes)):
        print "=" * 80
        print "INDEX: %d" % i
        mask, value = arm_opcodes[i]    
        
        seen = set()
        
        for i in xrange(limit):
            opcode = get_masked_random(mask, value)
            if opcode in seen:
                continue
            
            seen.add(opcode)
            
            if (opcode & mask) != value:
                continue
            
            opcode = opcode | 0xe0000000
            #opcode = 0xe2bc93fb
            try:
                ins = disassembler.disassemble(opcode, ARMMode.ARM)
                
            except UnpredictableInstructionException, e:
                #print "Unpredictable instruction"
                continue
            
            except NotImplementedError, e:
                #print "Instruction not implemented"
                continue
            
            except InstructionNotImplementedException, e:
                continue
            
            print "Sending instruction 0x%.8x (%30s) ... " % (opcode, ins),
            response = client.message(struct.pack("<L", opcode))
            
            if response == "ERROR":
                #print "Instruction %s caused an error on the Observer" % ins
                print "OBSERVER_ERROR"
                continue
                
            if response == "ILLEGAL":
                print "ILLEGAL"
                #print "Instruction %s is ILLEGAL" % ins
                #print "\tThis opcode %.8x should not disassemble" % opcode
                continue
            
            if response == "TIMEOUT":
                print "TIMEOUT"
                continue            
            
            # first line is pre execution context, second line is post execution context
            context = filter(None, response.split("\n"))
            pre_context = filter(None, context[0].split(",")) 
            post_context = filter(None, context[1].split(","))
            
            remote_pre_context = StringToContext(pre_context)
            remote_post_context = StringToContext(post_context)
            
            emulator.setContext(remote_pre_context)
            
            try:
                emulator.emulate(ins)
            except UnpredictableInstructionException:
                print "UNPREDICTABLE"
                continue
            except NotImplementedError:
                print "NOT_IMPLEMENTED"
                continue
            except RuntimeError:
                print "RuntimeError"
                continue
            except InstructionNotImplementedException, e:
                print "NOT_IMPLEMENTED"
                continue            
            
            local_post_context = emulator.getContext()

            ret = CompareContexts(local_post_context, remote_post_context)
            if not len(ret):
                print "MATCH"
                
            else:
                print "MISSMATCH"
                print
                print "Instruction %30s does NOT match (0x%.8x)" % (ins, opcode)
                for d in ret:
                    if d[0] == "flag":
                        print "\tLocal flag %10s value %.8x does not match remote value %.8x" \
                            % (ProcessorFlag(d[1]), d[2], d[3])
                    else:
                        print "\tLocal register %10s value %.8x does not match remote value %.8x" \
                            % (Register(d[1]), d[2], d[3])
                        
                    print "\tRemote:"
                    print "\t\tPRE  ", remote_pre_context.regs
                    print "\t\tPOST ", remote_post_context.regs

                    print "\tLocal:"
                    print "\t\tPRE  ", remote_pre_context.regs
                    print "\t\tPOST ", local_post_context.regs
                print

            
            #break
        break
