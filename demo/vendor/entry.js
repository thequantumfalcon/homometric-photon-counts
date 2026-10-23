// The only Three.js exports used by the optional offline illustration.
import {
  BufferGeometry, Color, DirectionalLight, Float32BufferAttribute,
  HemisphereLight, InstancedMesh, LineBasicMaterial, LineSegments,
  MeshStandardMaterial, Object3D, OrthographicCamera, Scene,
  SphereGeometry, Spherical, SRGBColorSpace, Vector3, WebGLRenderer,
} from 'three';
import { OrbitControls } from 'three/addons/controls/OrbitControls.js';

globalThis.PhotonThree = {
  BufferGeometry, Color, DirectionalLight, Float32BufferAttribute,
  HemisphereLight, InstancedMesh, LineBasicMaterial, LineSegments,
  MeshStandardMaterial, Object3D, OrthographicCamera, OrbitControls, Scene,
  SphereGeometry, Spherical, SRGBColorSpace, Vector3, WebGLRenderer,
};
