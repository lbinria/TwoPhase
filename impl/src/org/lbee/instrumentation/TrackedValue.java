package org.lbee.instrumentation;

public class TrackedValue<T> implements TrackableValue<T> {

    private final T value;
    private final String type;

    public TrackedValue(T value, String type) {
        this.value = value;
        this.type = type;
    }

    @Override
    public String toString() {
        return format(this.getType(), this.getValue());
    }

    protected String format(String type, T value) {
        return "{\"type\":\"" + type + "\",\"value\":" + value.toString() + "}";
    }

    @Override
    public T getValue() {
        return this.value;
    }

    @Override
    public String getType() {
        return this.type;
    }

}
