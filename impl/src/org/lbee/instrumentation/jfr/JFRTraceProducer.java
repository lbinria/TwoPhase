package org.lbee.instrumentation.jfr;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonPrimitive;
import org.lbee.instrumentation.FormalInstrumentation;
import org.lbee.instrumentation.TraceEvent;
import org.lbee.instrumentation.TraceProducer;
import org.lbee.instrumentation.TrackableValue;

import java.util.ArrayList;
import java.util.List;

// @TraceProducer(name="JFR")
public class JFRTraceProducer implements TraceProducer<JFRTraceEvent> {

    private FormalInstrumentation<?> instrumentation;
    private final List<TraceEvent> traces;

    public JFRTraceProducer() {
        this.traces = new ArrayList<>();
    }

    public void setIntrumentation(FormalInstrumentation<?> instrumentation) {
        this.instrumentation = instrumentation;
    }

    @Override
    public void commit(long clock) {

        for (TraceEvent trace : this.traces) {
            trace.setClock(clock);
            trace.commit();
        }

        this.traces.clear();
    }

    @Override
    public JFRTraceEvent produce(String operator, String name, TrackableValue<?>[] args, long clock) {
        String strArgs = serializeValues(args);
        System.out.printf("%s - Trace event: `%s %s (%s)`.\n", clock, operator, name, strArgs);
        JFRTraceEvent trace = new JFRTraceEvent(this.instrumentation.getGuid(), operator, name, strArgs, clock);
        this.traces.add(trace);
        return trace;
    }

    //
    private String serializeValues(TrackableValue<?>... values) {

        final JsonArray jsonArgs = new JsonArray();

        for (TrackableValue<?> value : values) {
            jsonArgs.add(this.serializeValue(value));
        }

        return jsonArgs.toString();
    }

    private JsonObject serializeValue(TrackableValue<?> value) {

        final JsonElement jsonValue =
            switch (value.getType()) {
                case "string" -> new JsonPrimitive((String)value.getValue());
                case "bool" -> new JsonPrimitive((Boolean) value.getValue());
                case "int" -> new JsonPrimitive((Number) value.getValue());
                case "record" -> new JsonPrimitive((Number) value.getValue());
                default -> null; // TODO should raise an exception
            }
        ;

        final JsonObject jsonObject = new JsonObject();
        jsonObject.add("type", new JsonPrimitive(value.getType()));
        jsonObject.add("value", jsonValue);
        return jsonObject;
    }

    /*
    private JsonObject serializeRecord() {

    }

     */

}
