name = "ARMv7_Specification.txt"

def validate_decoding_length():
    i = 0
    skip = True
    for line in open(name):
        i += 1
        if line == "\n":
            skip = True
            continue

        if skip:
            skip = False
            continue

        s = 0
        for a in line[:-1].split()[1:]:
            if "#" in a:
                b, c = a.split("#")
                s += int(c)

            else:
                s += len(a)

        if not s in [16, 32]:
            print i
            print line[:-1], "->", s

validate_decoding_length()