package org.lbee.instrumentation;

import java.util.Map;

public interface TrackableValue {

    String getType();
    Map<String, String> getProperties();
    Map<String, TrackableValue> getDynamicProperties();

}
