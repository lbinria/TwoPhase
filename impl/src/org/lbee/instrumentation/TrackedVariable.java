package org.lbee.instrumentation;

public abstract class TrackedVariable {

    private String name;
    private TraceProducer<?> traceProducer;

    public TrackedVariable() {
    }

    public void setName(String name) {
        this.name = name;
    }

    public String getName() { return this.name; }

    public void setTraceProducer(TraceProducer<?> traceProducer) {
        this.traceProducer = traceProducer;
    }

    protected void apply(String operator, TrackedValue... args) throws TraceProducerException {
        this.traceProducer.produce(operator, this.name, args, 0);
    }

}
