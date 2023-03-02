package org.lbee.instrumentation.tla.value;

import org.lbee.instrumentation.TracedValue;
import org.lbee.instrumentation.TracedValueProperty;
import org.lbee.instrumentation.TrackedValue;

@TracedValue(type = "string")
public class TLAStringValue extends TrackedValue {

    @TracedValueProperty(name="value")
    public String value;

    public TLAStringValue(String value) {
        this.value = value;
    }

}
