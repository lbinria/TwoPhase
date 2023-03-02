package org.lbee.tools;

import com.google.gson.*;
import jdk.jfr.consumer.RecordedEvent;
import jdk.jfr.consumer.RecordingFile;
import tlc2.value.ValueOutputStream;
import tlc2.value.impl.*;
import util.UniqueString;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class JFRSerializer {

    record Tuple(String name, long clock) { }

    public static void main(final String[] args) throws IOException {
        //String strPath = args.length > 0 ? args[0] : "app.jfr";

        System.out.printf("Start serializing from '%s'...\n", String.join(", ", args));

        // Read JFR events from files
        final List<RecordedEvent> recordedEvents = new ArrayList<>();
        for (String path : args) {
            recordedEvents.addAll(RecordingFile.readAllEvents(Path.of(path)));
        }

        // TODO set out with last arg
        serializeTrace(recordedEvents, Paths.get("Trace.bin"));
    }

    private static Value jsonToValue(String json) {
        // Read json
        JsonArray jsonArray = JsonParser.parseString(json).getAsJsonArray();
        // Convert all args
        Value[] values = jsonArray.asList().stream().map(jsonElement -> convertJsonObject(jsonElement.getAsJsonObject())).toArray(Value[]::new);
        // Return as tuple
        return new TupleValue(values);
    }

    private static Value convertJsonObject(JsonObject jsonObject) {

        final String type = jsonObject.get("_type").getAsString();
        final JsonElement jsonElement = jsonObject.get("value");

        return
        switch (type) {
            case "string" -> new StringValue(jsonElement.getAsString());
            case "bool" -> new BoolValue(jsonElement.getAsBoolean());
            case "int" -> IntValue.gen(jsonElement.getAsInt());
            case "record" -> recordFromJsonObject(jsonObject);
            default -> new StringValue(""); // TODO raise exception here !
        };

    }

    private static Value recordFromJsonObject(JsonObject jsonObject) {
        UniqueString[] names = jsonObject.entrySet().stream().filter(e -> !e.getKey().equals("_type") && e.getValue() != JsonNull.INSTANCE).map(e -> UniqueString.uniqueStringOf(e.getKey())).toArray(UniqueString[]::new);
        Value[] values = jsonObject.entrySet().stream().filter(e -> !e.getKey().equals("_type") && e.getValue() != JsonNull.INSTANCE).map(e -> convertJsonObject(e.getValue().getAsJsonObject())).toArray(Value[]::new);
        return new RecordValue(names, values, false);
    }


    private static void serializeTrace(final List<RecordedEvent> events, final Path out) throws IOException {

        final String senderName = "sender";
        final String keyName = "key";
        final String argsName = "args";
        final String clockName = "clock";
        final String opName = "op";

        // Prepare "record" names
        final UniqueString[] names = {
                UniqueString.uniqueStringOf(keyName),
                UniqueString.uniqueStringOf(opName),
                UniqueString.uniqueStringOf(argsName)
        };


        final UniqueString[] syncEventNames = {
                UniqueString.uniqueStringOf(opName),
                UniqueString.uniqueStringOf(argsName)
        };

        // Filter TLA events only
        // and order events chronologically
        final Stream<RecordedEvent> tlaEvents = events.stream().filter(e -> e.getEventType().getName().equals("app.JFRTraceEvent")).sorted(new Comparator<RecordedEvent>() {
            @Override
            public int compare(RecordedEvent o1, RecordedEvent o2) {
                //return o1.getStartTime().compareTo(o2.getStartTime());
                return Long.compare(o1.getLong(clockName), o2.getLong(clockName));
            }
        });



        // Group log by clock and process name
        final Map<Tuple, List<RecordedEvent>> tlaEventsGrouped = tlaEvents.collect(Collectors.groupingBy(e -> new Tuple(e.getString(senderName), e.getLong(clockName))));
        // Get groups as list of lists of events
        final List<List<RecordedEvent>> tlaEventsList = new ArrayList<>(tlaEventsGrouped.values().stream().toList());

        // Sort group by min date
        tlaEventsList.sort((a, b) -> {
            long minTimeA = Collections.min(a.stream().map(e -> e.getLong(clockName)).toList());
            long minTimeB = Collections.min(b.stream().map(e -> e.getLong(clockName)).toList());
            return Long.compare(minTimeA, minTimeB);
        });

        System.out.printf("Parsing %s TLA sync events to %s.\n", tlaEventsList.size(), out);

        final ArrayList<Value> tuples = new ArrayList<>(tlaEventsList.size());

        int i = 1;
        // Get events occurred at the same clock time
        for (List<RecordedEvent> clockEvents : tlaEventsList) {

            final ArrayList<RecordValue> records = new ArrayList<>(clockEvents.size());
            final ArrayList<UniqueString> keyNames = new ArrayList<>(clockEvents.size());

            System.out.printf("\n---- Sync event %s ----\n", i++);

            for (RecordedEvent event : clockEvents) {
                if (!event.getEventType().getName().equals("app.JFRTraceEvent"))
                    continue;

                // Convert args
                final String json = event.getString(argsName);
                final Value args = jsonToValue(json);

                // Get field values
                final Value[] syncEventValues = {
                        new StringValue(event.getString(opName)),
                        args
                };

                // Create record
                final RecordValue r = new RecordValue(syncEventNames, syncEventValues, false);
                records.add(r);
                keyNames.add(UniqueString.uniqueStringOf(event.getString(keyName)));
                System.out.printf("%s - %s - %s -> %s %s (%s).\n", event.getStartTime(), event.getLong(clockName), event.getString(senderName), event.getString(opName), event.getString(keyName), event.getString(argsName));
            }

            // Put records in record
            final UniqueString[] keyNamesArray = keyNames.toArray(UniqueString[]::new);
            final Value[] recordsArray = records.toArray(Value[]::new);
            final RecordValue eventRecord = new RecordValue(keyNamesArray, recordsArray, false);

            tuples.add(eventRecord);
        }

        final Value[] v = tuples.toArray(new Value[0]);
        final TupleValue eventTuple = new TupleValue(v);

        final ValueOutputStream vos = new ValueOutputStream(out.toFile(), true);
        // Do not normalize TupleValue because normalization depends on the actual
        // UniqueString#internTable.

        //final Assignment a = new Assignment("Bob", new String[]{"x"}, "x");


        eventTuple.write(vos);

        vos.close();

        System.out.printf("Successfully serialized to %s.\n", out);
    }

}
