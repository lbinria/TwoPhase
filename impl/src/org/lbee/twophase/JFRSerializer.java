package org.lbee.twophase;

import jdk.jfr.consumer.RecordedEvent;
import jdk.jfr.consumer.RecordingFile;
import tlc2.value.ValueOutputStream;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.TupleValue;
import tlc2.value.impl.Value;
import util.UniqueString;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.time.Instant;
import java.util.*;
import java.util.function.Predicate;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class JFRSerializer {

    record Tuple(String name, long clock) { }

    public static void main(final String[] args) throws IOException {
        String strPath = args.length > 0 ? args[0] : "app.jfr";

        System.out.printf("Start serializing at '%s'...\n", strPath);

        final List<RecordedEvent> recordedEvents = RecordingFile
                .readAllEvents(Paths.get(args.length > 0 ? args[0] : "app.jfr"));

        // Order events chronologically based on the system's clock (that hopefully has
        // sufficient precision).
        // TODO: Logical clock instead of real/global clock.
        recordedEvents.sort(new Comparator<RecordedEvent>() {
            @Override
            public int compare(RecordedEvent o1, RecordedEvent o2) {
                return o1.getStartTime().compareTo(o2.getStartTime());
            }
        });

        serializeTrace(recordedEvents, Paths.get(args.length > 1 ? args[1] : "Trace.bin"));
    }

    private static void serializeTrace(final List<RecordedEvent> events, final Path out) throws IOException {

        final String senderName = "sender";
        final String keyName = "key";
        final String valName = "val";

        // Prepare "record" names
        final UniqueString[] names = {
                UniqueString.uniqueStringOf(senderName),
                UniqueString.uniqueStringOf(keyName),
                UniqueString.uniqueStringOf(valName)
        };

        // Filter TLA events only
        final Stream<RecordedEvent> tlaEvents = events.stream().filter(e -> e.getEventType().getName().equals("app.TLAEvent"));
        // Group log by clock and process name
        final Map<Tuple, List<RecordedEvent>> tlaEventsGrouped = tlaEvents.collect(Collectors.groupingBy(e -> new Tuple(e.getString(senderName), e.getLong("clock"))));
        // Get groups as list of lists of events
        final List<List<RecordedEvent>> tlaEventsList = new ArrayList<>(tlaEventsGrouped.values().stream().toList());

        // Sort group by min date
        tlaEventsList.sort((a, b) -> {
            Instant minTimeA = Collections.min(a.stream().map(RecordedEvent::getStartTime).toList());
            Instant minTimeB = Collections.min(b.stream().map(RecordedEvent::getStartTime).toList());
            return minTimeA.compareTo(minTimeB);
        });

        System.out.printf("Parsing %s TLA sync events to %s.\n", tlaEventsList.size(), out);

        final ArrayList<Value> tuples = new ArrayList<>(tlaEventsList.size());

        int i = 1;
        // Get events occurred at the same clock time
        for (List<RecordedEvent> clockEvents : tlaEventsList) {

            final ArrayList<RecordValue> records = new ArrayList<>(clockEvents.size());

            System.out.printf("\n---- Sync event %s ----\n", i++);

            for (RecordedEvent event : clockEvents) {
                if (event.getEventType().getName().equals("app.TLAEvent")) {
                    // Get field values
                    Value[] values = {
                            new StringValue(event.getString(senderName)),
                            new StringValue(event.getString(keyName)),
                            new StringValue(event.getString(valName))
                    };

                    // Create record
                    final RecordValue r = new RecordValue(names, values, false);
                    records.add(r);

                    System.out.printf("%s - %s - %s.%s = %s.\n", event.getStartTime(), event.getLong("clock"), event.getString(senderName), event.getString(keyName), event.getString(valName));
                }
            }

            // Put records in tuple
            final TupleValue eventClockTuple = new TupleValue(records.toArray(new RecordValue[0]));

            tuples.add(eventClockTuple);
        }

        final Value[] v = tuples.toArray(new Value[0]);
        final TupleValue eventTuple = new TupleValue(v);

        final ValueOutputStream vos = new ValueOutputStream(out.toFile(), true);
        // Do not normalize TupleValue because normalization depends on the actual
        // UniqueString#internTable.
        eventTuple.write(vos);
        vos.close();

        System.out.printf("Successfully serialized to %s.\n", out);
    }

}
