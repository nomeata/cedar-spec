@x("\u{8}6666")
@zs10("\0\0\0\0\0\0")
permit(
  principal == a::"\0",
  action == Action::"action",
  resource
) when {
  (true && (resource is a)) && (action in a::"\0")
};
