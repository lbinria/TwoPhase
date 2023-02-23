package org.lbee.instrumentation.tla;

import org.lbee.instrumentation.*;

public abstract class TLAVariable<TValue extends FormalValue<?>> implements TrackedVariable {

    private String name;
    private TraceProducer<?> traceProducer;
    private final String type;


    public TLAVariable() {
        // Get annotation of formal value linked to variable
        FormalValueType valueTypeAnnot = FormalValue.class.getAnnotation(FormalValueType.class);
        //this.type = valueTypeAnnot.type();
        this.type = "";
    }

    @Override
    public abstract String getType();
    /*
    public String getType() {
        return this.type;
    }
    */


    @Override
    public void setName(String name) {
        this.name = name;
    }

    @Override
    public void setTraceProducer(TraceProducer<?> traceProducer) {
        this.traceProducer = traceProducer;
    }

    @Override
    public void apply(String operator, Object value) {
        this.traceProducer.produce(operator, this.name, value.toString(), this.getType(), 0);
    }

    public abstract void set(TValue value);



}
