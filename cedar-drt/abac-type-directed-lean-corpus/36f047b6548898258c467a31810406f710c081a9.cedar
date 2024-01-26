forbid(
  principal is a,
  action == Action::"action",
  resource is a in a::"\0\0\0\0\0r\0+\0\u{e}\0\0\0\0\0\0\0\0+\0\0\0\0\0\0\0"
) when {
  true && ({"": {"": []}} == {"": {"": true}})
};
