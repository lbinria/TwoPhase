package org.lbee.instrumentation;

public interface TrackableVariable<TValue extends TrackableValue<?>> {

    void setName(String name);
    void setTraceProducer(TraceProducer<?> traceProducer);
    void apply(String operator, TValue... value);

}
