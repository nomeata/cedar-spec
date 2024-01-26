permit(
  principal is a in a::"\u{16}66",
  action == Action::"action",
  resource is a in a::"\u{16}66"
) when {
  ((true && ([].contains([]))) && true) && (!(resource in action))
};
