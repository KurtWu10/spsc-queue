def get_function(lines: list[str], name: str) -> list[str]:
    start = lines.index(f"{name}:\n")
    end = lines.index("\t.cfi_endproc\n", start)
    return lines[start:end+1]

def preprocess(lines: list[str]) -> list[str]:
    ret = []
    for line in lines:
        end = line.find("//")
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
        line = line.replace('\t', ' ').rstrip().replace("beq", "b.eq")
        ret.append(line)
    ret.append(f".return{index}:")

    # fix labels
    for i in range(len(ret)):
        if ret[i].endswith(':'):
            label = ret[i][:-1]
            for j in range(len(ret)):
                ret[j] = ret[j].replace(label, f"{label}__{index}")

    return ret

def preprocess_threads(threads: list[list[str]], index: int, height: int) -> list[list[str]]:
    return [' ' + line for line in threads + [f"b .return{index}"] + [""] * (height - len(threads) + 1)]

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
        "AArch64 SPSC (weak)\n"
        "{\n"
        "  int queue1[3]; int queue2[3];\n"
        "  0: x19 = queue1; 0: x20 = queue2;\n"
        "  1: x19 = queue1; 1: x20 = queue2;\n"
        "}"
    )

    threads = [
        [
            "mov x0, x19",
            "mov x1, #42",
            "bl enqueue",
            "mov x21, x0",
            "mov x0, x20",
            "bl dequeue",
            "mov x22, x0",
        ],
        [
            "mov x0, x20",
            "mov x1, #43",
            "bl enqueue",
            "mov x21, x0",
            "mov x0, x19",
            "bl dequeue",
            "mov x22, x0",
        ]
    ]
    threads_height = max(len(thread) for thread in threads)

    functions = get_function(preprocess(lines), "enqueue") + get_function(preprocess(lines), "dequeue")

    output([postprocess(preprocess_threads(threads[i], i, threads_height) + functions, i) for i in range(2)])

    print(r"exists (0: x21 = 0 /\ 0: x22 = -1 /\ 1: x21 = 0 /\ 1: x22 = -1)")
