permit(
  principal is a in a::"\u{16}666",
  action == Action::"action",
  resource is a in a::"\u{16}666"
) when {
  ((true && ([if false then [] else [], []].contains([]))) && false) && false
};
