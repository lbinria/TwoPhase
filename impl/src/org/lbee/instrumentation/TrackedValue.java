package org.lbee.instrumentation;

public abstract class TrackedValue<T> implements TrackableValue<T> {

    @Override
    public String toString() {
        return format(this.getType(), this.getValue());
    }

    public String format(String type, T value) {
        return "{\"type\":\"" + type + ",\"value\":" + value.toString() + "}";
    }

}
