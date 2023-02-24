package org.lbee.instrumentation;

public interface TrackableVariable {

    String getType();
    void setName(String name);
    void setTraceProducer(TraceProducer<?> traceProducer);
    void apply(String operator, Object... value);

}
