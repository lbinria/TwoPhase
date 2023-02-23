package org.lbee.instrumentation;

public interface TraceProducer<TOut extends TraceEvent> {

    void setIntrumentation(FormalInstrumentation<?> instrumentation);
    TOut produce(String op, String name, Object value, String type, long clock);
    void commit(long clock);
}
