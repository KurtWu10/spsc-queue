def get_function(lines: list[str], name: str) -> list[str]:
    start = lines.index(f"{name}:\n")
    end = lines.index("\t.cfi_endproc\n", start)
    return lines[start:end+1]

def preprocess(lines: list[str]) -> list[str]:
    ret = []
    for line in lines:
        end = line.find("#")
        if end != -1:
            line = line[:end]
        if line.strip():
            ret.append(line.rstrip() + '\n')
    return ret

def postprocess(lines: list[str], index: int) -> list[str]:
    ret = []
    for line in lines:
        if line.lstrip().startswith('.') and not line.endswith(':\n'):
            continue
        line = line.replace('\t', ' ').rstrip()
        if line.strip() == "ret":
            line = f" j .return{index}"
        ret.append(line)
    ret.append(f".return{index}:")
    for i in range(len(ret)):
        if ret[i].startswith('.'):
            label = ret[i].strip()[:-1]
            for j in range(len(ret)):
                ret[j] = ret[j].replace(label, label[1:])
    return ret

def output(threads: list[list[str]]):
    widths = [max(len(line) for line in lines) + 1 for lines in threads]
    height = max(len(lines) for lines in threads)
    print('|'.join(f" P{i}{' ' * (widths[i] - len(f' P{i}'))}" for i in range(len(threads))) + ';')
    for i in range(height):
        for j in range(len(threads)):
            if i < len(threads[j]):
                print(threads[j][i] + ' ' * (widths[j] - len(threads[j][i])), end='')
            else:
                print(' ' * widths[j], end='')

            if j < len(threads) - 1:
                print('|', end='')

        print(';')

if __name__ == "__main__":
    import sys

    with open(sys.argv[1]) as f:
        lines = f.readlines()

    print(
        "RISCV SPSC\n"
        "{\n"
        "  int queue[3];\n"
        "  0: a0 = queue; 0: a1 = 42;\n"
        "  1: a0 = queue;\n"
        "}"
    )

    output([
        postprocess(get_function(preprocess(lines), name), i)
        for i, name in enumerate(["enqueue", "dequeue"])
    ])

    print(r"forall (1: a0 = -1 \/ 1: a0 = 42)")
