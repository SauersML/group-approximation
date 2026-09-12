# Length nine and the remaining area-eight face partitions

The necklace-based exact classifier ran on MSI and returned

```text
LENGTH 9 ORBIT_REPRESENTATIVES 2241906
CONSERVATIVE_SURVIVORS 0
UNKNOWN_BLOCKS 0
```

Thus there is no odd corner identity of length nine.

An area-eight survivor has one odd internal face and one odd outer face.
Since all six face lengths sum to 24, the remaining possibilities are

```text
2,2,2,2,5,11       2,2,2,3,4,11
1,2,2,2,6,11       1,2,2,4,4,11
2,2,2,2,3,13       1,2,2,2,4,13
1,2,2,2,2,15.
```

Every internal 2-face is one of the four exact gate squares.  Contracting
two, three, or four such digons reduces the cubic ribbon core from eight
vertices to four, two, or zero vertices.  Therefore length eleven requires
only one exceptional two-digon four-vertex classification plus three
smaller-core cases; lengths thirteen and fifteen are entirely controlled by
three/four-digon contractions.  No blind length-eleven-to-fifteen alphabet
enumeration is needed.
