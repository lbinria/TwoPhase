package org.lbee.twophase;

import java.io.*;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class TLAConfigTemplate {

    private final Map<String, String> constantNameValues;
    private final Pattern regex;

    public TLAConfigTemplate(Map<String, String> constants) {
        this.constantNameValues = constants;
        // Regex used to process template variables
        this.regex = Pattern.compile("\\{\\{(?<constantName>\\w+)}}");
    }

    /**
     * Generate a config file for TLA replacing some variables by given values (in map)
     * @param path Template file path
     * @throws IOException
     */
    public void generate(String path) throws IOException {
        // Read file and replace template variables
        final List<String> lines = read(path);
        // Write file
        write(path.replace(".template", ""), lines);
    }

    /**
     * Write a .cfg configuration file for TLA given lines to write
     * @param path Configuration file path
     * @param lines String lines to write
     * @throws IOException
     */
    private void write(String path, List<String> lines) throws IOException {
        final File file = new File(path);
        final BufferedWriter writer = new BufferedWriter(new FileWriter(file));

        for (String line : lines) {
            writer.write(line);
        }

        writer.close();
    }

    private List<String> read(String path) throws IOException {
        // Open file
        final File file = new File(path);
        final BufferedReader reader = new BufferedReader(new FileReader(file));
        // List of processed lines
        final ArrayList<String> processedLines = new ArrayList<>();
        // Current line
        String line;

        while ((line = reader.readLine()) != null) {
            final Matcher matcher = this.regex.matcher(line);
            if (!matcher.find()) {
                processedLines.add(line + "\n");
                continue;
            }

            final String constantName = matcher.group("constantName");

            // Search into map
            if (!this.constantNameValues.containsKey(constantName))
            {
                // TODO Throw
            }

            // Get value of template variable
            final String constantValue = this.constantNameValues.get(constantName);
            // Replace template variable by its value
            final String replacedLine = matcher.replaceAll(constantValue);
            // Append processed line
            processedLines.add(replacedLine + "\n");
        }
        reader.close();

        return processedLines;
    }

}
