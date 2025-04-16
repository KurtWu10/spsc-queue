#include <assert.h>
#include <stdatomic.h>
#include <stdlib.h>
#include <threads.h>

#define CAPACITY 1

typedef struct {
    int tail;
    int head;
    int buffers[CAPACITY];
    mtx_t mutex;
} Queue;

int enqueue(Queue * queue, int buffer) {
    if (mtx_lock(&queue->mutex) != thrd_success) {
        exit(1);
    }

    const int tail_val = queue->tail;
    const int head_val = queue->head;

    if (tail_val - head_val == CAPACITY) {
        if (mtx_unlock(&queue->mutex) != thrd_success) {
            exit(1);
        }

        return -1;
    } else {
        queue->buffers[tail_val % CAPACITY] = buffer;
        queue->tail = tail_val + 1;

        if (mtx_unlock(&queue->mutex) != thrd_success) {
            exit(1);
        }

        return 0;
    }
}

int dequeue(Queue * queue) {
    if (mtx_lock(&queue->mutex) != thrd_success) {
        exit(1);
    }

    const int head_val = queue->head;
    const int tail_val = queue->tail;

    if (tail_val - head_val == 0) {
        if (mtx_unlock(&queue->mutex) != thrd_success) {
            exit(1);
        }

        return -1;
    } else {
        int buffer = queue->buffers[head_val % CAPACITY];
        queue->head = head_val + 1;

        if (mtx_unlock(&queue->mutex) != thrd_success) {
            exit(1);
        }

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

    if (mtx_init(&queue1.mutex, mtx_plain) != thrd_success) {
        return 1;
    }
    if (mtx_init(&queue2.mutex, mtx_plain) != thrd_success) {
        return 1;
    }

    Args args = {
        .queue1 = &queue1,
        .queue2 = &queue2,
    };

    thrd_t thread;
    if (thrd_create(&thread, forked_thread, (void *) &args) != thrd_success) {
        return 1;
    }

    int ret1 = enqueue(args.queue1, 43);
    int ret2 = dequeue(args.queue2);

    thrd_join(thread, NULL);

    mtx_destroy(&queue2.mutex);
    mtx_destroy(&queue1.mutex);

    assert(!(ret1 == 0 && ret2 == -1 && args.ret1 == 0 && args.ret2 == -1));

    return 0;
}
