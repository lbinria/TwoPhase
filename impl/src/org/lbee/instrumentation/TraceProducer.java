package org.lbee.instrumentation;

public interface TraceProducer<TOut extends TraceEvent> {

    void setIntrumentation(FormalInstrumentation<?> instrumentation);
    TOut produce(String op, String name, TrackableValue[] args, long clock) throws TraceProducerException;
    void commit(long clock);
}
