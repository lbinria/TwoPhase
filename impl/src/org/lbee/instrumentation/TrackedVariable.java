package org.lbee.instrumentation;

public abstract class TrackedVariable implements TrackableVariable {

    private String name;
    private TraceProducer<?> traceProducer;

    public TrackedVariable() {
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
    public void apply(String operator, TrackableValue... args) throws TraceProducerException {
        this.traceProducer.produce(operator, this.name, args, 0);
    }

}
