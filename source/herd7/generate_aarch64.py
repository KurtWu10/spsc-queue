from common import get_function, output, preprocess, postprocess

def arch_postprocess(lines: list[str]) -> list[str]:
    return [line.replace("beq", "b.eq") for line in lines]

def preprocess_threads(threads: list[list[str]], height: int) -> list[list[str]]:
    return [' ' + line for line in threads + ["b return"] + [""] * (height - len(threads) + 1)]

def print_test0(lines: list[str]) -> None:
    print(
        "AArch64 SPSC\n"
        "{\n"
        "  int queue[3];\n"
        "  0: X19 = queue;\n"
        "  1: X19 = queue;\n"
        "}"
    )

    threads = [
        [
            "mov x0, x19",
            "mov x1, #42",
            "bl enqueue",
        ],
        [
            "mov x0, x19",
            "bl dequeue",
        ]
    ]
    threads_height = max(len(thread) for thread in threads)

    functions = get_function(preprocess(lines, "//"), "enqueue") + get_function(preprocess(lines, "//"), "dequeue")

    output([
        postprocess(arch_postprocess(preprocess_threads(threads[i], threads_height) + functions), i)
        for i in range(2)
    ])

    print(r"forall (1: x0 = -1 \/ 1: x0 = 42)")

def print_test1(lines: list[str]) -> None:
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

    functions = get_function(preprocess(lines, "//"), "enqueue") + get_function(preprocess(lines, "//"), "dequeue")

    output([arch_postprocess(postprocess(preprocess_threads(threads[i], threads_height) + functions, i)) for i in range(2)])

    print(r"exists (0: x21 = 0 /\ 0: x22 = -1 /\ 1: x21 = 0 /\ 1: x22 = -1)")

if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument("filename", type=str)
    parser.add_argument("--id", type=int, default=0)
    args = parser.parse_args()

    with open(args.filename) as f:
        lines = f.readlines()

    if args.id == 0:
        print_test0(lines)
    elif args.id == 1:
        print_test1(lines)
    else:
        raise ValueError("unknown 'id'")
