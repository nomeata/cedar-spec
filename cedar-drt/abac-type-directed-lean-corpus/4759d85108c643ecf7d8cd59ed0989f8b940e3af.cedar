permit(
  principal,
  action in [],
  resource
) when {
  (true && ([[[], []], [false, false]].containsAll([]))) && false
};
