package org.lbee.instrumentation;

import java.lang.reflect.Field;
import java.util.Arrays;
import java.util.Map;
import java.util.stream.Collectors;

@TracedValue(type = "unknown", name = "")
// TODO rename
public class TrackedValue implements TrackableValue {

    private final String type;
    private final Map<String, String> properties;


    @Override
    public Map<String, String> getProperties() { return this.properties; }

    public TrackedValue() {
        // Get type of value from annotation
        TracedValue tracedValue = this.getClass().getAnnotation(TracedValue.class);
        this.type = tracedValue.type();
        // Get fields annotations
        this.properties = Arrays.stream(this.getClass().getFields()).collect(Collectors.toMap(Field::getName, vm -> vm.getAnnotation(TracedValueProperty.class).name()));
    }

    @Override
    public String getType() {
        return this.type;
    }

}
