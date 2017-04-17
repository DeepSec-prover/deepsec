(function () {
    'use strict';
    window.DAG = {
        displayGraph: function(graph, svgParent, id, subid, trace) {
            var nodes = graph.nodes;
            var links = graph.links;

            var graphElem = svgParent.children('g').get(0);
            var svg = d3.select(graphElem);
            var renderer = new dagreD3.Renderer();
            var layout = dagreD3.layout().rankDir('TP');
            renderer.layout(layout).run(dagreD3.json.decode(nodes, links), svg.append('g'));

            // Adjust SVG height to content
            var main = svgParent.find('g > g');

            if (trace <= 1) {
              var h = main.get(0).getBoundingClientRect().height;
              var l = main.get(0).getBoundingClientRect().width;
              var scale = h/l;
              var newWidth;
              var newHeight;
              if (l < 80) {
                newWidth = 80;
                newHeight = 80*scale;
              } else {
                newWidth = l+40;
                newHeight = h+40;
              }
              svgParent.height(newHeight);
              svgParent.width(newWidth);
              if (trace == 1) {
                window['height_' + id + 'e' + subid] = newHeight;
                window['width_' + id + 'e' + subid] = newWidth;
              }
            } else {
              svgParent.height(window['height_' + id + 'e' + subid]);
              svgParent.width(window['width_' + id + 'e' + subid]);
            }

            // Zoom
            d3.select(svgParent.get(0)).call(d3.behavior.zoom().on('zoom', function() {
                var ev = d3.event;
                svg.select('g')
                    .attr('transform', 'translate(' + ev.translate + ') scale(' + ev.scale + ')');
            }));

            if (trace > 1) {
              document.getElementById('dag-' + id + 'e' + subid + 'e' + trace).style.display = 'none';
            }
        }
    };
})();

function loaddata(file) {
  'use strict';
  jQuery(function () {
      // load script with graph data
      var fileName = window.location.search ? window.location.search.slice(1) : (''+file);
      var dataScript = document.createElement('script');
      dataScript.src = fileName;
      document.body.appendChild(dataScript);
  });
}
