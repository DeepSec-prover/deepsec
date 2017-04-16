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
              var newHeight = h + 40;
              var newWidth = l + 40;
              newHeight = newHeight < 80 ? 80 : newHeight;
              newWidth = newWidth < 80 ? 80 : newWidth;
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

function previous(id) {
  var counter = window['counter_' + id];
  var max_number = window['max_number_actions_' + id]

  // Verification if the previous button needs to be disabled or not
  if (counter == 2) {
    document.getElementById('previous-' + id).disabled = true;
  }
  document.getElementById('next-' + id).disabled = false;

  // Display previous information
  document.getElementById('desc-' + id + 'e' + (counter-1)).style.display = 'inline';
  document.getElementById('dag-' + id + 'e' + (counter-1)).style.display = 'block';
  document.getElementById('renaming-' + id + 'e' + (counter-1)).style.display = 'block';

  // Hide current information
  document.getElementById('desc-' + id + 'e' + counter).style.display = 'none';
  document.getElementById('dag-' + id + 'e' + counter).style.display = 'none';
  document.getElementById('renaming-' + id + 'e' + counter).style.display = 'none';
  var action = document.getElementById('action-' + id + 'e' + counter);
  if (action != null) {
    action.style.display = 'none';
  }

  // Set new counter
  window['counter_' + id] = counter - 1;
}

function next(id) {
  var counter = window['counter_' + id];
  var max_number = window['max_number_actions_' + id]

  // Verification if the next button needs to be disabled or not
  if (counter == max_number - 1) {
    document.getElementById('next-' + id).disabled = true;
  }
  document.getElementById('previous-' + id).disabled = false;

  // Hide current information
  document.getElementById('desc-' + id + 'e' + counter).style.display = 'none';
  document.getElementById('dag-' + id + 'e' + counter).style.display = 'none';
  document.getElementById('renaming-' + id + 'e' + counter).style.display = 'none';

  // Display previous information
  document.getElementById('desc-' + id + 'e' + (counter+1)).style.display = 'inline';
  document.getElementById('dag-' + id + 'e' + (counter+1)).style.display = 'block';
  document.getElementById('renaming-' + id + 'e' + (counter+1)).style.display = 'block';
  var action = document.getElementById('action-' + id + 'e' + (counter+1));
  if (action != null) {
    action.style.display = 'block';
  }

  // Set new counter
  window['counter_' + id] = counter + 1;
}
