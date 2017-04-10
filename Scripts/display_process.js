(function () {
    'use strict';
    window.DAG = {
        displayGraph: function (graph, dagNameElem, svgElem) {
            dagNameElem.text(graph.name);
            this.renderGraph(graph, svgElem);
        },

        renderGraph: function(graph, svgParent) {
            var nodes = graph.nodes;
            var links = graph.links;

            var graphElem = svgParent.children('g').get(0);
            var svg = d3.select(graphElem);
            var renderer = new dagreD3.Renderer();
            var layout = dagreD3.layout().rankDir('TP');
            renderer.layout(layout).run(dagreD3.json.decode(nodes, links), svg.append('g'));

            // Adjust SVG height to content
            var main = svgParent.find('g > g');
            var h = main.get(0).getBoundingClientRect().height;
            var l = main.get(0).getBoundingClientRect().width;
            var newHeight = h + 40;
            var newWidth = l + 40;
            newHeight = newHeight < 80 ? 80 : newHeight;
            newWidth = newWidth < 80 ? 80 : newWidth;
            svgParent.height(newHeight);
            svgParent.width(newWidth);

            // Zoom
            d3.select(svgParent.get(0)).call(d3.behavior.zoom().on('zoom', function() {
                var ev = d3.event;
                svg.select('g')
                    .attr('transform', 'translate(' + ev.translate + ') scale(' + ev.scale + ')');
            }));
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
