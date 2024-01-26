forbid(
  principal is a in a::"\0\0",
  action == Action::"action",
  resource is a
) when {
  true && ({"": "II\u{1b}III"} == {"": {"\0r": false}})
};
