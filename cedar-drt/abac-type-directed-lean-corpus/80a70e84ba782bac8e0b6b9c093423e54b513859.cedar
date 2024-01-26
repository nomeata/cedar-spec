permit(
  principal == a::"6",
  action == Action::"action",
  resource == a::"6"
) when {
  true && ([action in action].containsAll(if ((ip("d49d:9d9d:9d9d:6900:0:9d9d:9d69:6365/126")).isMulticast()) then [] else [[], [], []]))
};
