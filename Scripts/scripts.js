function previous(id) {
  var counter = window['counter_' + id];
  var max_number = window['max_number_actions_' + id]

  // Verification if the previous button needs to be disabled or not
  if (counter == 2) {
    document.getElementById('previous-' + id).disabled = true;
  }
  document.getElementById('next-' + id).disabled = false;

  // Display previous information
  document.getElementById('desc-' + id + 'e' + (counter-1)).style.display = 'inline-block';
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
  document.getElementById('desc-' + id + 'e' + (counter+1)).style.display = 'inline-block';
  document.getElementById('dag-' + id + 'e' + (counter+1)).style.display = 'block';
  document.getElementById('renaming-' + id + 'e' + (counter+1)).style.display = 'block';
  var action = document.getElementById('action-' + id + 'e' + (counter+1));
  if (action != null) {
    action.style.display = 'block';
  }

  // Set new counter
  window['counter_' + id] = counter + 1;
}

function previous_expansed(id) {
  var counter = window['counter_' + id];
  var max_number = window['max_number_actions_' + id]

  // Verification if the previous button needs to be disabled or not
  if (counter == 2) {
    document.getElementById('previous-' + id).disabled = true;
  }
  document.getElementById('next-' + id).disabled = false;

  // Display previous information
  document.getElementById('desc-' + id + 'e' + (counter-1)).style.display = 'inline-block';
  document.getElementById('expansed' + id + 'e' + (counter-1)).style.display = 'block';

  // Hide current information
  document.getElementById('desc-' + id + 'e' + counter).style.display = 'none';
  document.getElementById('expansed' + id + 'e' + counter).style.display = 'none';
  var action = document.getElementById('action-' + id + 'e' + counter);
  if (action != null) {
    action.style.display = 'none';
  }

  // Set new counter
  window['counter_' + id] = counter - 1;
}

function next_expansed(id) {
  var counter = window['counter_' + id];
  var max_number = window['max_number_actions_' + id]

  // Verification if the next button needs to be disabled or not
  if (counter == max_number - 1) {
    document.getElementById('next-' + id).disabled = true;
  }
  document.getElementById('previous-' + id).disabled = false;

  // Hide current information
  document.getElementById('desc-' + id + 'e' + counter).style.display = 'none';
  document.getElementById('expansed' + id + 'e' + counter).style.display = 'none';

  // Display previous information
  document.getElementById('desc-' + id + 'e' + (counter+1)).style.display = 'inline-block';
  document.getElementById('expansed' + id + 'e' + (counter+1)).style.display = 'block';
  var action = document.getElementById('action-' + id + 'e' + (counter+1));
  if (action != null) {
    action.style.display = 'block';
  }

  // Set new counter
  window['counter_' + id] = counter + 1;
}
