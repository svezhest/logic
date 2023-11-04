import sys


def parse(_line):
    global line, pos
    line = _line + '#'
    pos = 0

    def skip(s):
        # print(pos)
        global line, pos
        if line.startswith(s, pos):
            pos += len(s)
            return True
        return False

    def e():
        x = dij()
        if skip('->'):
            x = ['->', x, e()]
        return x

    def dij():
        x = con()
        while skip('|'):
            x = ['|', x, con()]
        return x

    def con():
        x = nt()
        while skip('&'):
            x = ['&', x, nt()]
        return x

    def nt():
        global pos, line
        if skip('('):
            x = e()
            skip(')')
            return x
        if skip('!'):
            return ['!', nt()]
        x = ''
        while line[pos].isdigit() or line[pos].isalpha() or line[pos] == '\'':
            x += line[pos]
            pos += 1
        return x

    gamma = [e()]

    if gamma[0] == '':
        gamma.clear()

    while line[pos] == ',':
        pos += 1
        gamma.append(e())

    pos += 1
    expected = e()

    proof = []
    while pos < len(line) and line[pos] == ',':
        pos += 1
        proof.append(e())

    num = 0

    def to_string_natural(l):
        if len(l) > 1:
            if l[0] == '!':
                return '(' + to_string_natural(l[1]) + '->' + '_|_' + ')'
            if len(l) > 2:
                if l[0] == '|':
                    return '(' + to_string_natural(l[1]) + '|' + to_string_natural(l[2]) + ')'
                if l[0] == '&':
                    return to_string_natural(l[1]) + '&' + to_string_natural(l[2])
                if l[0] == '->':
                    return '(' + to_string_natural(l[1]) + '->' + to_string_natural(l[2]) + ')'
        return str(l)

    axiomatic_proof = {}

    def is_assumption(s):
        if s in gamma:
            axiomatic_proof[str(s)] = ['ax']
            # print("assumption", prnt(s))
            return True
        return False

    def is_mp(s):
        for n in proof[:num]:
            for m in proof[:num]:
                if len(n) > 2 and n[0] == '->' and n[1] == m and n[2] == s:
                    axiomatic_proof[str(s)] = ['mp', n, m]
                    # print("mp", prnt(n), "\\", prnt(m))
                    return True
        return False

    def is_axiom(s):
        def check_type(_s, type):
            if len(_s) <= 1:
                return False
            if _s[0] != type:
                return False
            return len(_s) == 3 or type == '!'

        if check_type(s, '->') and check_type(s[2], '->') and s[1] == s[2][2]:
            axiomatic_proof[str(s)] = ['+i', s[1], s[2][1]]
            # print("a -> b -> a")
        elif check_type(s, '->') \
                and check_type(s[1], '->') \
                and check_type(s[2], '->') \
                and check_type(s[2][1], '->') \
                and check_type(s[2][2], '->') \
                and check_type(s[2][1][2], '->') \
                and s[1][1] == s[2][1][1] == s[2][2][1] \
                and s[1][2] == s[2][1][2][1] \
                and s[2][1][2][2] == s[2][2][2]:
            axiomatic_proof[str(s)] = ['-i', s[2][1][1], s[2][1][2][1], s[2][1][2][2]]
            # print("(a -> b) -> (a -> b -> c) -> (a -> c)")
        elif check_type(s, '->') \
                and check_type(s[2], '->') \
                and check_type(s[2][2], '&') \
                and s[1] == s[2][2][1] and s[2][1] == s[2][2][2]:
            axiomatic_proof[str(s)] = ['+c', s[1], s[2][1]]
            # print("a -> b -> a & b")
        elif check_type(s, '->') \
                and check_type(s[1], '&') \
                and s[1][1] == s[2]:
            axiomatic_proof[str(s)] = ['-ca', s[1][1], s[1][2]]
            # print("a & b -> a")
        elif check_type(s, '->') \
                and check_type(s[1], '&') \
                and s[1][2] == s[2]:
            axiomatic_proof[str(s)] = ['-cb', s[1][1], s[1][2]]
            # print("a & b -> b")
        elif check_type(s, '->') \
                and check_type(s[2], '|') \
                and s[1] == s[2][1]:
            axiomatic_proof[str(s)] = ['+da', s[2][1], s[2][2]]
            # print("a -> a | b")
        elif check_type(s, '->') \
                and check_type(s[2], '|') \
                and s[1] == s[2][2]:
            axiomatic_proof[str(s)] = ['+db', s[2][1], s[2][2]]
            # print("b -> a | b")
        elif check_type(s, '->') \
                and check_type(s[1], '->') \
                and check_type(s[2], '->') \
                and check_type(s[2][1], '->') \
                and check_type(s[2][2], '->') \
                and check_type(s[2][2][1], '|') \
                and s[1][2] == s[2][1][2] == s[2][2][2] \
                and s[1][1] == s[2][2][1][1] \
                and s[2][1][1] == s[2][2][1][2]:
            axiomatic_proof[str(s)] = ['-d', s[1][1], s[2][1][1], s[1][2]]
            # print("(a -> c) -> (b -> c) -> (a | b -> c)") 
        elif check_type(s, '->') \
                and check_type(s[1], '->') \
                and check_type(s[2], '->') \
                and check_type(s[2][1], '->') \
                and check_type(s[2][2], '!') \
                and check_type(s[2][1][2], '!') \
                and s[1][1] == s[2][1][1] == s[2][2][1] \
                and s[1][2] == s[2][1][2][1]:
            axiomatic_proof[str(s)] = ['+f', s[1][1], s[1][2]]
            # print("(a -> b) -> (a -> !b) -> !a")
        elif check_type(s, '->') \
                and check_type(s[2], '->') \
                and check_type(s[2][1], '!') \
                and s[1] == s[2][1][1]:
            axiomatic_proof[str(s)] = ['-f', s[1], s[2][2]]
            # print("a -> !a -> b")
        else:
            return False
        return True

    # print(gamma)
    # print(proof)

    for p in proof:
        if not (is_axiom(p) or is_mp(p) or is_assumption(p)):
            print("Proof is incorrect at line ", num + 2)
            return False
        num += 1

    if expected != proof[-1]:
        print("The proof does not prove the required expression")
        return False

    ans = []

    def naturalize(s, depth, _gamma):

        def natural_format(rule, _depth, __gamma, current):
            ans.append("[{}] {}|-{} [{}]"
                       .format(_depth, ','.join([to_string_natural(x) for x in __gamma]),
                               to_string_natural(current), rule))

        _type = axiomatic_proof[str(s)][0]
        if _type == 'mp':
            natural_format("E->", depth, gamma, s)
            for x in axiomatic_proof[str(s)][2:0:-1]:
                naturalize(x, depth + 1, _gamma)
        elif _type == 'ax':
            natural_format("Ax", depth, gamma, s)
        elif _type == '+i':
            _a, _b = axiomatic_proof[str(s)][1:]
            natural_format("I->", depth, gamma, s)
            natural_format("I->", depth + 1, gamma + [_a], ['->', _b, _a])
            natural_format("Ax", depth + 2, gamma + [_b, _a], _a)
        elif _type == '-i':
            _a, _b, _c = axiomatic_proof[str(s)][1:]
            natural_format("I->", depth, gamma, s)
            natural_format("I->", depth + 1, gamma + [['->', _a, _b]],
                           ['->', ['->', _a, ['->', _b, _c]], ['->', _a, _c]])
            natural_format("I->", depth + 2, gamma + [['->', _a, _b], ['->', _a, ['->', _b, _c]]],
                           ['->', _a, _c])
            natural_format("E->", depth + 3, gamma + [['->', _a, _b], ['->', _a, ['->', _b, _c]], _a],
                           _c)
            natural_format("E->", depth + 4, gamma + [['->', _a, _b], ['->', _a, ['->', _b, _c]], _a],
                           _b)
            natural_format("Ax", depth + 5, gamma + [['->', _a, _b], ['->', _a, ['->', _b, _c]], _a],
                           _a)
            natural_format("Ax", depth + 5, gamma + [['->', _a, _b], ['->', _a, ['->', _b, _c]], _a],
                           ['->', _a, _b])
            natural_format("E->", depth + 4, gamma + [['->', _a, _b], ['->', _a, ['->', _b, _c]], _a],
                           ['->', _b, _c])
            natural_format("Ax", depth + 5, gamma + [['->', _a, _b], ['->', _a, ['->', _b, _c]], _a],
                           _a)
            natural_format("Ax", depth + 5, gamma + [['->', _a, _b], ['->', _a, ['->', _b, _c]], _a],
                           ['->', _a, ['->', _b, _c]])
        elif _type == '+c':
            _a, _b = axiomatic_proof[str(s)][1:]
            natural_format("I->", depth, gamma, s)
            natural_format("I->", depth + 1, gamma + [_a],
                           ['->', _b, ['&', _a, _b]])
            natural_format("I&", depth + 2, gamma + [_a, _b],
                           ['&', _a, _b])
            natural_format("Ax", depth + 3, gamma + [_a, _b],
                           _b)
            natural_format("Ax", depth + 3, gamma + [_a, _b],
                           _a)
        elif _type == '-ca':
            _a, _b = axiomatic_proof[str(s)][1:]
            natural_format("I->", depth, gamma, s)
            natural_format("El&", depth + 1, gamma + [['&', _a, _b]],
                           _a)
            natural_format("Ax", depth + 2, gamma + [['&', _a, _b]], ['&', _a, _b])
        elif _type == '-cb':
            _a, _b = axiomatic_proof[str(s)][1:]
            natural_format("I->", depth, gamma, s)
            natural_format("Er&", depth + 1, gamma + [['&', _a, _b]],
                           _b)
            natural_format("Ax", depth + 2, gamma + [['&', _a, _b]], ['&', _a, _b])
        elif _type == '+da':
            _a, _b = axiomatic_proof[str(s)][1:]
            natural_format("I->", depth, gamma, s)
            natural_format("Il|", depth + 1, gamma + [_a],
                           ['|', _a, _b])
            natural_format("Ax", depth + 2, gamma + [_a], _a)
        elif _type == '+db':
            _a, _b = axiomatic_proof[str(s)][1:]
            natural_format("I->", depth, gamma, s)
            natural_format("Ir|", depth + 1, gamma + [_b],
                           ['|', _a, _b])
            natural_format("Ax", depth + 2, gamma + [_b], _b)
        elif _type == '-d':
            _a, _b, _c = axiomatic_proof[str(s)][1:]
            natural_format("I->", depth, gamma, s)
            natural_format("I->", depth + 1, gamma + [['->', _a, _c]],
                           ['->', ['->', _b, _c], ['->', ['|', _a, _b], _c]])
            natural_format("I->", depth + 2, gamma + [['->', _a, _c], ['->', _b, _c]],
                           ['->', ['|', _a, _b], _c])
            natural_format("E|", depth + 3, gamma + [['->', _a, _c], ['->', _b, _c], ['|', _a, _b]],
                           _c)
            natural_format("Ax", depth + 4, gamma + [['->', _a, _c], ['->', _b, _c], ['|', _a, _b]],
                           ['|', _a, _b])
            natural_format("E->", depth + 4, gamma + [['->', _a, _c], ['->', _b, _c], ['|', _a, _b], _b],
                           _c)
            natural_format("Ax", depth + 5, gamma + [['->', _a, _c], ['->', _b, _c], ['|', _a, _b], _b],
                           _b)
            natural_format("Ax", depth + 5, gamma + [['->', _a, _c], ['->', _b, _c], ['|', _a, _b], _b],
                           ['->', _b, _c])
            natural_format("E->", depth + 4, gamma + [['->', _a, _c], ['->', _b, _c], ['|', _a, _b], _a],
                           _c)
            natural_format("Ax", depth + 5, gamma + [['->', _a, _c], ['->', _b, _c], ['|', _a, _b], _a],
                           _a)
            natural_format("Ax", depth + 5, gamma + [['->', _a, _c], ['->', _b, _c], ['|', _a, _b], _a],
                           ['->', _a, _c])

        elif _type == '+f':
            _a, _b = axiomatic_proof[str(s)][1:]
            natural_format("I->", depth, gamma, s)
            natural_format("I->", depth + 1, gamma + [['->', _a, _b]],
                           ['->', ['->', _a, ['!', _b]], ['!', _a]])
            natural_format("I->", depth + 2, gamma + [['->', _a, _b], ['->', _a, ['!', _b]]],
                           ['!', _a])
            natural_format("E->", depth + 3, gamma + [['->', _a, _b], ['->', _a, ['!', _b]], _a],
                           '_|_')
            natural_format("E->", depth + 4, gamma + [['->', _a, _b], ['->', _a, ['!', _b]], _a],
                           _b)
            natural_format("Ax", depth + 5, gamma + [['->', _a, _b], ['->', _a, ['!', _b]], _a],
                           _a)
            natural_format("Ax", depth + 5, gamma + [['->', _a, _b], ['->', _a, ['!', _b]], _a],
                           ['->', _a, _b])
            natural_format("E->", depth + 4, gamma + [['->', _a, _b], ['->', _a, ['!', _b]], _a],
                           ['!', _b])
            natural_format("Ax", depth + 5, gamma + [['->', _a, _b], ['->', _a, ['!', _b]], _a],
                           _a)
            natural_format("Ax", depth + 5, gamma + [['->', _a, _b], ['->', _a, ['!', _b]], _a],
                           ['->', _a, ['!', _b]])
        elif _type == '-f':
            _a, _b = axiomatic_proof[str(s)][1:]
            natural_format("I->", depth, gamma, s)
            natural_format("I->", depth + 1, gamma + [_a],
                           ['->', ['!', _a], _b])
            natural_format("E_|_", depth + 2, gamma + [_a, ['!', _a]],
                           _b)
            natural_format("E->", depth + 3, gamma + [_a, ['!', _a]],
                           '_|_')
            natural_format("Ax", depth + 4, gamma + [_a, ['!', _a]],
                           _a)
            natural_format("Ax", depth + 4, gamma + [_a, ['!', _a]],
                           ['!', _a])

    naturalize(expected, 0, gamma)

    for x in ans[::-1]:
        print(x)

    return True


def main():
    sys.setrecursionlimit(2 ** 30)
    line = ''

    with sys.stdin as f:
        cmm = False
        for x in f.read():
            if not cmm and x == '\n':
                line += ','
                cmm = True
            if not x.isspace():
                line += x
                cmm = False

    i = len(line) - 1
    while line[i] == ',' or line[i].isspace():
        i -= 1

    line = line[:i + 1]

    line = line.replace("|-", "~")

    parse(line)


if __name__ == '__main__':
    main()
