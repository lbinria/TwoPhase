package org.lbee.instrumentation;

import java.lang.reflect.Field;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import java.util.stream.Collectors;

@TracedValue(type = "value"/*, name = ""*/)
public class TrackedValue implements TrackableValue {

    private final String type;
    private final Map<String, String> properties;
    private final Map<String, TrackableValue> dynamicProperties;

    @Override
    public Map<String, String> getProperties() { return this.properties; }

    @Override
    public Map<String, TrackableValue> getDynamicProperties() { return this.dynamicProperties; }

    public TrackedValue() {
        this(Map.of());
    }

    public TrackedValue(Map<String, TrackableValue> dynamicProperties) {
        // Get type of value from annotation
        TracedValue tracedValue = this.getClass().getAnnotation(TracedValue.class);
        this.type = tracedValue.type();
        // Get fields annotations
        this.properties = Arrays.stream(this.getClass().getFields()).collect(Collectors.toMap(Field::getName, vm -> vm.getAnnotation(TracedValueProperty.class).name()));
        this.dynamicProperties = dynamicProperties;
    }


    @Override
    public String getType() {
        return this.type;
    }

}
