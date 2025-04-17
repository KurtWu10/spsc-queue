from common import get_function, output, preprocess, postprocess

def arch_postprocess(lines: list[str]) -> list[str]:
    return [(" j return" if line.lstrip() == "ret" else line) for line in lines]

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
        postprocess(arch_postprocess(get_function(preprocess(lines, "#"), name)), i)
        for i, name in enumerate(["enqueue", "dequeue"])
    ])

    print(r"forall (1: a0 = -1 \/ 1: a0 = 42)")
