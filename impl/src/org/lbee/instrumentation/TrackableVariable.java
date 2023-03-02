package org.lbee.instrumentation;

public interface TrackableVariable {

    String getName();
    void setName(String name);
    void setTraceProducer(TraceProducer<?> traceProducer);
    void apply(String operator, TrackableValue... value) throws TraceProducerException;

}
