package org.lbee.instrumentation;

import java.util.HashMap;
import java.util.Map;

public abstract class TrackedVariable<TValue extends TrackableValue> implements TrackableVariable<TValue> {

    private String name;
    private TraceProducer<?> traceProducer;
    private final Map<String, Operator> operators;

    public TrackedVariable() {
        this.operators = new HashMap<>();
    }

    @Override
    public void setName(String name) {
        this.name = name;
    }

    @Override
    public String getName() { return this.name; }

    @Override
    public void setTraceProducer(TraceProducer<?> traceProducer) {
        this.traceProducer = traceProducer;
    }

    @Override
    public void apply(String operator, TValue... args) throws TraceProducerException {
        this.traceProducer.produce(operator, this.name, args, 0);
    }

    public abstract void set(TValue value) throws TraceProducerException;

}
