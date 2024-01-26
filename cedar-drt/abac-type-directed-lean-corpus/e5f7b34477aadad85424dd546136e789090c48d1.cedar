forbid(
  principal is a,
  action == Action::"action",
  resource is a in a::"\0\0"
) when {
  true && ({"": {"": []}} == {"": {"\0": false}})
};
