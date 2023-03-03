package org.lbee.instrumentation;

public interface TraceProducer<TOut extends TraceEvent> {

    void setIntrumentation(TraceInstrumentation<?> instrumentation);
    TOut produce(String op, String name, TrackedValue[] args, long clock) throws TraceProducerException;
    void commit(long clock);
}
