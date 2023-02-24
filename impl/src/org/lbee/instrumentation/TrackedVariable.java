package org.lbee.instrumentation;

import java.util.Arrays;
import java.util.Map;
import java.util.stream.Collectors;

public abstract class TrackedVariable<TValue extends TrackableValue<?>> implements TrackableVariable {

    private String name;
    private TraceProducer<?> traceProducer;
    private final String type;
    private final Map<String, Operator> operators;

    public TrackedVariable() {
        this.type = "";
        this.operators = Map.of();
    }

    // TODO remove
    @Override
    public abstract String getType();

    @Override
    public void setName(String name) {
        this.name = name;
    }

    @Override
    public void setTraceProducer(TraceProducer<?> traceProducer) {
        this.traceProducer = traceProducer;
    }

    @Override
    public void apply(String operator, Object... args) {
        // TODO check operator existence
        //Operator op = this.operators.get(operator);
        String strValues = "[" + Arrays.stream(args).map(Object::toString).collect(Collectors.joining(",")) + "]";
        this.traceProducer.produce(operator, this.name, strValues, this.getType(), 0);
    }

    public void applyFromMethod(String methodName, Object... args) {
        Operator op = this.operators.get(methodName);
        this.apply(op.targetOperator(), args);
    }

    public abstract void set(TValue value);

    public void settt(Object... args) {
        this.applyFromMethod("set", args);
    }


}
