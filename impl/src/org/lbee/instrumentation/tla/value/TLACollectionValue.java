package org.lbee.instrumentation.tla.value;

import org.lbee.instrumentation.TracedValueProperty;
import org.lbee.instrumentation.TrackedValue;

import java.util.List;

public abstract class TLACollectionValue<T extends TrackedValue> extends TrackedValue {

    @TracedValueProperty(name = "value")
    public List<T> value;

}
