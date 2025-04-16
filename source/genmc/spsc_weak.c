#include <assert.h>
#include <stdatomic.h>
#include <threads.h>

#define CAPACITY 1

typedef struct {
    atomic_int tail;
    atomic_int head;
    int buffers[CAPACITY];
} Queue;

int enqueue(Queue * queue, int buffer) {
    const int tail_val = atomic_load_explicit(&queue->tail, memory_order_relaxed);
    const int head_val = atomic_load_explicit(&queue->head, memory_order_acquire);

    if (tail_val - head_val == CAPACITY) {
        return -1;
    } else {
        queue->buffers[tail_val % CAPACITY] = buffer;
        atomic_store_explicit(&queue->tail, tail_val + 1, memory_order_release);
        return 0;
    }
}

int dequeue(Queue * queue) {
    const int head_val = atomic_load_explicit(&queue->head, memory_order_relaxed);
    const int tail_val = atomic_load_explicit(&queue->tail, memory_order_acquire);

    if (tail_val - head_val == 0) {
        return -1;
    } else {
        int buffer = queue->buffers[head_val % CAPACITY];
        atomic_store_explicit(&queue->head, head_val + 1, memory_order_release);
        return buffer;
    }
}

typedef struct {
    Queue * queue1;
    Queue * queue2;
    int ret1;
    int ret2;
} Args;

int forked_thread(void * argsp) {
    Args * args = (Args *) argsp;

    args->ret1 = enqueue(args->queue2, 42);
    args->ret2 = dequeue(args->queue1);
    return 0;
}

int main() {
    Queue queue1 = {0};
    Queue queue2 = {0};

    Args args = {
        .queue1 = &queue1,
        .queue2 = &queue2,
    };

    thrd_t thrd;
    if (thrd_create(&thrd, forked_thread, (void *) &args) != thrd_success) {
        return 1;
    }

    int ret1 = enqueue(args.queue1, 43);
    int ret2 = dequeue(args.queue2);

    thrd_join(thrd, NULL);

    assert(!(ret1 == 0 && ret2 == -1 && args.ret1 == 0 && args.ret2 == -1));

    return 0;
}
