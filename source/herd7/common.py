def get_function(lines: list[str], name: str) -> list[str]:
    start = lines.index(f"{name}:")
    end = lines.index(" .cfi_endproc", start)
    return lines[start:end+1]

def preprocess(lines: list[str], comment_token: str) -> list[str]:
    ret = []
    for line in lines:
        end = line.find(comment_token)
        if end != -1:
            line = line[:end]
        if line.strip():
            ret.append(line.rstrip().replace('\t', ' '))
    return ret

def postprocess(lines: list[str], index: int) -> list[str]:
    ret = lines.copy() + ["return:"]

    # fix labels
    for i in range(len(ret)):
        if ret[i].endswith(':'):
            label = ret[i][:-1]
            for j in range(len(ret)):
                ret[j] = ret[j].replace(label, f"{label.lstrip('.')}__{index}")

    ret = [line for line in ret if not line.lstrip().startswith('.')]

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
