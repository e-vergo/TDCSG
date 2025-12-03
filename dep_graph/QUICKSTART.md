# TDCSG Dependency Graph - Quick Start

## Open the Visualization

**Recommended method (avoids CORS issues):**
```bash
cd dep_graph
./serve.sh
# Then open http://localhost:8000/index.html in your browser
```

**Alternative method (may require file selection due to CORS):**
```bash
open /Users/eric/Documents/GitHub/TDCSG/dep_graph/index.html
# If you see "Load Graph Data" dialog, select graph.json from the file picker
```

## What You'll See

- **362 colored nodes** representing TDCSG declarations
- **2076 edges** showing dependencies
- **3 gold nodes** with red borders (main theorems)
- **Purple gradient background**
- **Interactive controls** (top-left)

## Basic Usage

### Explore a Node
1. **Click any node** → Info panel opens (right side)
2. See: full name, type, documentation, dependencies
3. **Click GitHub link** → Jump to source code
4. **Click dependency** → Jump to that node

### Navigate
- **Scroll**: Zoom in/out
- **Click + drag background**: Pan
- **Click + drag node**: Reposition
- **Type in search box**: Filter nodes by name

### Save Your Layout
1. Arrange nodes as desired (drag them)
2. Click **"Save Layout"** button
3. Move downloaded `positions.json` to this directory
4. Refresh browser → positions persist

### Reset
Click **"Reset View"** to fit all nodes

## Color Guide

- **Coral red** (#FF6B6B): Theorems
- **Turquoise** (#4ECDC4): Definitions
- **Light coral** (#FFA07A): Lemmas
- **Yellow** (#FFD93D): Inductives
- **Gold + red border**: Main theorems (3 total)

## Shape Guide

- **Ellipse**: Theorems, lemmas
- **Rectangle**: Definitions
- **Diamond**: Inductives

## Main Theorems (Gold + Red Border)

1. **GG5_At_Critical_radius**
2. **StatementOfTheorem**
3. **GG5_infinite_at_critical_radius**

These are the key results of the TDCSG formalization.

## Tips

- **Initial load takes 5-10 seconds** (force-directed layout computation)
- **After layout, save positions** for instant reload
- **Use search** to find specific declarations quickly
- **Zoom in** to read node labels clearly
- **GitHub links** open source code in new tab

## Keyboard Shortcuts

None - use mouse/trackpad for interaction.

## Browser Compatibility

Works in modern browsers:
- Chrome 90+
- Firefox 88+
- Safari 14+

## Troubleshooting

**"Error Loading Graph" or "Load Graph Data" dialog appears**:
- This is due to browser CORS restrictions with `file://` protocol
- Solution: Use `./serve.sh` instead (starts local server)
- Alternative: Select `graph.json` from the file picker when prompted

**Graph doesn't appear**: Check browser console for errors (F12 or Cmd+Option+I)

**Layout looks wrong**: Delete `positions.json` and refresh

**Nodes overlap**: Drag nodes apart, then save layout

**Search doesn't work**: Type in the search box at top-left

## Files

- **`index.html`**: Main page (open this)
- **`graph.js`**: Visualization logic
- **`styles.css`**: Visual styling
- **`graph.json`**: Full dependency data (362 nodes)
- **`positions.json`**: Saved layout (create with "Save Layout")

## Example Workflow

1. Open `index.html`
2. Wait for layout to compute (~10 seconds)
3. Click "StatementOfTheorem" (main theorem)
4. Read documentation in info panel
5. Click GitHub link → view source
6. Click dependency "r_crit" → jump to that node
7. Search "orbit" → see all orbit-related declarations
8. Drag nodes to clean up layout
9. Click "Save Layout" → move file
10. Refresh → layout persists

## Data Statistics

- **Declarations**: 362 total
- **Dependencies**: 2076 edges
- **Main theorems**: 3 highlighted
- **Files covered**: All TDCSG/*.lean files

## Documentation

See full documentation:
- **`README.md`**: Complete user guide
- **`TESTING.md`**: Testing results
- **`IMPLEMENTATION_REPORT.md`**: Technical details
- **`DELIVERY_SUMMARY.md`**: Implementation summary

## Support

For issues or questions, refer to the comprehensive documentation files in this directory.

---

**Ready to explore? Run:**
```bash
cd dep_graph
./serve.sh
# Then open http://localhost:8000/index.html
```
