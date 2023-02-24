package org.lbee.instrumentation;

import java.util.Arrays;
import java.util.Map;
import java.util.stream.Collectors;

public abstract class TrackedVariable<TValue extends TrackableValue<?>> implements TrackableVariable<TValue> {

    private String name;
    private TraceProducer<?> traceProducer;
    private final String type;
    private final Map<String, Operator> operators;

    public TrackedVariable() {
        this.type = "";
        this.operators = Map.of();
    }

    @Override
    public void setName(String name) {
        this.name = name;
    }

    @Override
    public void setTraceProducer(TraceProducer<?> traceProducer) {
        this.traceProducer = traceProducer;
    }

    @Override
    public void apply(String operator, TValue... args) {
        // TODO check operator existence
        //Operator op = this.operators.get(operator);
        String strValues = "[" + Arrays.stream(args).map(arg -> "{\"value\":"+ arg.getValue().toString() + ", \"type\":\"" + arg.getType() + "\"}").collect(Collectors.joining(",")) + "]";
        this.traceProducer.produce(operator, this.name, strValues, 0);
    }

    public void applyFromMethod(String methodName, TValue... args) {
        Operator op = this.operators.get(methodName);
        // TODO Check consistency between op and value type
        this.apply(op.targetOperator(), args);
    }

    public abstract void set(TValue value);

    // TODO remove TEST
    public void settt(TValue... args) {
        this.applyFromMethod("set", args);
    }


}
