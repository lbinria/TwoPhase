package org.lbee.instrumentation;

public interface TrackedVariable {

    String getType();
    void setName(String name);
    void setTraceProducer(TraceProducer<?> traceProducer);
    void apply(String operator, Object value);

}
