package org.lbee.instrumentation;

public interface TrackableValue<T> {

    T getValue();
    String getType();

    // TODO add default value

}
