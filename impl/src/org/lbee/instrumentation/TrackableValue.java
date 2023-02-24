package org.lbee.instrumentation;

public interface TrackableValue<T> {

    T getValue();
    String getType();

    static TrackableValue<?> defaultValue() {
        return null;
    }

}
