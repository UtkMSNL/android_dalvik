struct Thread;
struct FifoBuffer;

void offPushAllStacks(struct FifoBuffer* sfb, struct FifoBuffer* fb);

void offPullAllStacks(struct FifoBuffer* sfb);

void offPushStack(struct FifoBuffer* sfb, struct FifoBuffer* fb, struct Thread* thread);

struct Thread* offPullStack(struct FifoBuffer* sfb, u4 tid);

#ifdef DEBUG
bool offCheckBreakFrames();

int offDebugStack(const struct Thread* thread);
#endif

#define CHECK_BREAK_FRAMES() assert(offCheckBreakFrames())
