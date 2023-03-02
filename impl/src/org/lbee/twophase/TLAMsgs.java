package org.lbee.twophase;

import org.lbee.instrumentation.TracedValue;
import org.lbee.instrumentation.TracedValueProperty;
import org.lbee.instrumentation.tla.value.TLARecordValue;
import org.lbee.instrumentation.tla.value.TLAStringValue;

@TracedValue(type="record")
public class TLAMsgs extends TLARecordValue {

    @TracedValueProperty(name="type")
    public TLAStringValue type;

    @TracedValueProperty(name="rm")
    public TLAStringValue resourceManagerName;

    public TLAMsgs(TLAStringValue type, TLAStringValue resourceManagerName) {
        this.type = type;
        this.resourceManagerName = resourceManagerName;
    }

    public TLAMsgs(TLAStringValue type) {
        this.type = type;
    }

}
