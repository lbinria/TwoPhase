package org.lbee.instrumentation;

import java.lang.reflect.Field;
import java.util.Arrays;
import java.util.Map;
import java.util.stream.Collectors;

public abstract class TrackedValue {

    protected final Map<String, String> properties;
    //private final Map<String, TrackedValue> dynamicProperties;

    public Map<String, String> getProperties() { return this.properties; }

    //public Map<String, TrackedValue> getDynamicProperties() { return this.dynamicProperties; }

    public TrackedValue() {
        // Get type of value from annotation
        // TracedValue tracedValue = this.getClass().getAnnotation(TracedValue.class);
        // this.type = tracedValue.type();
        // Get fields annotations
        this.properties = Arrays.stream(this.getClass().getFields()).collect(Collectors.toMap(Field::getName, vm -> vm.getAnnotation(TracedValueProperty.class).name()));
    }

    public abstract String getType();

}
