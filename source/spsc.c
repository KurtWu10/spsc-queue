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

int forked_thread(void * queuep) {
    Queue * queue = (Queue *) queuep;
    enqueue(queue, 42);
    return 0;
}

int main() {
    Queue queue = {0};

    thrd_t thrd;
    if (thrd_create(&thrd, forked_thread, (void *) &queue) != thrd_success) {
        return 1;
    }

    int ret = dequeue(&queue);

    thrd_join(thrd, NULL);

    assert(ret == -1 || ret == 42);

    return 0;
}
