package org.lbee.instrumentation.jfr;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonPrimitive;
import org.lbee.instrumentation.*;

import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

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
    public JFRTraceEvent produce(String operator, String name, TrackableValue[] args, long clock) throws TraceProducerException {
        try {
            String strArgs = serializeValues(args);
            System.out.printf("%s - Trace event: `%s %s (%s)`.\n", clock, operator, name, strArgs);
            JFRTraceEvent trace = new JFRTraceEvent(this.instrumentation.getGuid(), operator, name, strArgs, clock);
            this.traces.add(trace);
            return trace;
        } catch (NoSuchFieldException | IllegalAccessException ex) {
            // TODO set inner exception in order to keep trace
            throw new TraceProducerException();
        }
    }

    //
    private String serializeValues(TrackableValue... values) throws NoSuchFieldException, IllegalAccessException {

        final JsonArray jsonArgs = new JsonArray();

        for (TrackableValue value : values) {
            jsonArgs.add(this.serializeValue(value));
        }

        return jsonArgs.toString();
    }

    private JsonObject serializeValue(TrackableValue value) throws NoSuchFieldException, IllegalAccessException {

        JsonObject jsonObject = new JsonObject();

        for (Map.Entry<String, String> property : value.getProperties().entrySet()) {

            Field field = value.getClass().getField(property.getKey());
            Object propertyValue = field.get(value);
            Class<?> propertyType = field.getType();

            final JsonElement jsonValue;
            if (propertyValue instanceof TrackableValue) {
                jsonValue = serializeValue((TrackableValue) propertyValue);
            }
            else {
                if (propertyType.equals(String.class))
                    jsonValue = new JsonPrimitive((String) propertyValue);
                else if (propertyType.equals(Boolean.class))
                    jsonValue = new JsonPrimitive((Boolean) propertyValue);
                else if (propertyType.equals(Integer.class))
                    jsonValue = new JsonPrimitive((Number) propertyValue);
                else
                    jsonValue = null;
            }

            jsonObject.add(property.getValue(), jsonValue);

        }

        jsonObject.add("_type", new JsonPrimitive(value.getType()));
        return jsonObject;
    }

}
