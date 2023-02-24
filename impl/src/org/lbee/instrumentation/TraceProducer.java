package org.lbee.instrumentation;

public interface TraceProducer<TOut extends TraceEvent> {

    void setIntrumentation(FormalInstrumentation<?> instrumentation);
    TOut produce(String op, String name, TrackableValue<?>[] args, long clock);
    void commit(long clock);
}
